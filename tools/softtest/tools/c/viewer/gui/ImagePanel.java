package softtest.tools.c.viewer.gui;

import java.awt.BorderLayout;
import java.awt.Graphics;
import java.awt.Image;
import java.awt.Point;
import java.awt.Toolkit;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.awt.event.MouseMotionListener;
import java.io.File;
import java.io.IOException;
import javax.imageio.ImageIO;
import javax.swing.BorderFactory;
import javax.swing.JFileChooser;
import javax.swing.JPanel;
import javax.swing.filechooser.FileNameExtensionFilter;

import softtest.tools.c.viewer.model.ViewerModel;
import softtest.tools.c.viewer.model.ViewerModelEvent;
import softtest.tools.c.viewer.model.ViewerModelListener;
import softtest.tools.c.viewer.util.NLS;


/**
 * 能够拖拽图片的面板
 */
public class ImagePanel extends JPanel implements ViewerModelListener {
	/**
	 * 
	 */
	private static final long serialVersionUID = -3159579588700151603L;
	
	private ViewerModel model;
	
	private DragStatus status = DragStatus.Ready; // 拖拽状态
	private Image image; // 要显示的图片
	private Point imagePosition = new Point(0, 0), // 图片的当前位置
			imageStartposition = new Point(0, 0), // 每次拖拽开始时图片的位置（也就是上次拖拽后的位置）
			mouseStartposition; // 每次拖拽开始时鼠标的位置

	private void init(String title) {
        model.addViewerModelListener(this);
        setBorder(BorderFactory.createTitledBorder(BorderFactory.createEtchedBorder(), title));
        setLayout(new BorderLayout());
    }
	
	//	liuli	2010.4.13
	//因为调用图工具添加了CG面板，在面板顶部显示的文字title与控制流图的不同，所以将显示文字作为参数传入
	public ImagePanel(ViewerModel m,String title) {
		this.model = m;
		addMouseListener(new MouseListener() {
			// 双击鼠标时打开图片
			public void mouseClicked(MouseEvent e) {
				if (e.getClickCount() == 2) {
					openImage();
				}
			}

			// 按下鼠标时，更改状态，并且记录拖拽起始位置。
			public void mousePressed(MouseEvent e) {
				if (status == DragStatus.Ready) {
					status = DragStatus.Dragging;
					mouseStartposition = e.getPoint();
					imageStartposition.setLocation(imagePosition.getLocation());
				}
			}

			// 松开鼠标时更改状态
			public void mouseReleased(MouseEvent e) {
				if (status == DragStatus.Dragging) {
					status = DragStatus.Ready;
				}
			}

			public void mouseEntered(MouseEvent e) {
			}

			public void mouseExited(MouseEvent e) {
			}
		});
		addMouseMotionListener(new MouseMotionListener() {
			// Java 有拖拽事件，在这个事件中移动图片位置
			public void mouseDragged(MouseEvent e) {
				if (status == DragStatus.Dragging) {
					moveImage(e.getPoint());
				}
			}

			public void mouseMoved(MouseEvent e) {
			}
		});
		init(title);
	}
	
	public ImagePanel(String imagefile) {
		openImage(imagefile);
		
		addMouseListener(new MouseListener() {
			// 双击鼠标时打开图片
			public void mouseClicked(MouseEvent e) {
				if (e.getClickCount() == 2) {
					openImage();
				}
			}

			// 按下鼠标时，更改状态，并且记录拖拽起始位置。
			public void mousePressed(MouseEvent e) {
				if (status == DragStatus.Ready) {
					status = DragStatus.Dragging;
					mouseStartposition = e.getPoint();
					imageStartposition.setLocation(imagePosition.getLocation());
				}
			}

			// 松开鼠标时更改状态
			public void mouseReleased(MouseEvent e) {
				if (status == DragStatus.Dragging) {
					status = DragStatus.Ready;
				}
			}

			public void mouseEntered(MouseEvent e) {
			}

			public void mouseExited(MouseEvent e) {
			}
		});
		addMouseMotionListener(new MouseMotionListener() {
			// Java 有拖拽事件，在这个事件中移动图片位置
			public void mouseDragged(MouseEvent e) {
				if (status == DragStatus.Dragging) {
					moveImage(e.getPoint());
				}
			}

			public void mouseMoved(MouseEvent e) {
			}
		});
	}
	
	public ImagePanel() {
		addMouseListener(new MouseListener() {
			// 双击鼠标时打开图片
			public void mouseClicked(MouseEvent e) {
				if (e.getClickCount() == 2) {
					openImage();
				}
			}

			// 按下鼠标时，更改状态，并且记录拖拽起始位置。
			public void mousePressed(MouseEvent e) {
				if (status == DragStatus.Ready) {
					status = DragStatus.Dragging;
					mouseStartposition = e.getPoint();
					imageStartposition.setLocation(imagePosition.getLocation());
				}
			}

			// 松开鼠标时更改状态
			public void mouseReleased(MouseEvent e) {
				if (status == DragStatus.Dragging) {
					status = DragStatus.Ready;
				}
			}

			public void mouseEntered(MouseEvent e) {
			}

			public void mouseExited(MouseEvent e) {
			}
		});
		addMouseMotionListener(new MouseMotionListener() {
			// Java 有拖拽事件，在这个事件中移动图片位置
			public void mouseDragged(MouseEvent e) {
				if (status == DragStatus.Dragging) {
					moveImage(e.getPoint());
				}
			}

			public void mouseMoved(MouseEvent e) {
			}
		});
	}

	/**
	 * 移动图片。实际上画图工作在 paintComponent() 中进行，这里只是计算图片位置，然后调用该方法。
	 * 
	 * @param point
	 *            当前的鼠标位置
	 */
	private void moveImage(Point point) {
		// 图片的当前位置等于图片的起始位置加上鼠标位置的偏移量。
		imagePosition.setLocation(imageStartposition.getX()
				+ (point.getX() - mouseStartposition.getX()),
				imageStartposition.getY()
						+ (point.getY() - mouseStartposition.getY()));
		repaint();
	}

	public void openImage(String imagefile) {
		if (imagefile != null) {
			// image = null;
			// this.repaint();
			try {
				image = ImageIO.read(new File(imagefile));

				// image = Toolkit.getDefaultToolkit().getImage(imagefile);
				// image.flush();
				// image.setAccelerationPriority(1);
				// this.imageUpdate(img, infoflags, x, y, w, h)
				if (image != null) {
					repaint();
					//JTabbedPane jtp = ((JTabbedPane) (this.getParent()));
				}
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
	}
	
	// 打开图片
	private void openImage() {
		System.out.println("Opening image...");
		File file = createFileChooser().getSelectedFile();
		if (file != null) {
			image = Toolkit.getDefaultToolkit()
					.getImage(file.getAbsolutePath());
			if (image != null) {
				this.repaint();
			}
		}
	}

	// 创建打开文件对话框
	private JFileChooser createFileChooser() {
		JFileChooser chooser = new JFileChooser();
		chooser.setDialogTitle("请选择图片文件...");
		chooser.addChoosableFileFilter(new FileNameExtensionFilter("常用图片格式",
				"jpg", "jpeg", "gif", "png"));
		chooser.showOpenDialog(this);
		return chooser;
	}

	@Override
	protected void paintComponent(Graphics g) {
		super.paintComponent(g);
		if (image != null) {
			g.drawImage(image, (int) imagePosition.getX(), (int) imagePosition
					.getY(), this);
		}
	}

	private enum DragStatus {
		Ready, Dragging
	}
	
	/**
     * @see ViewerModelListener#viewerModelChanged(ViewerModelEvent)
     */
    public void viewerModelChanged(ViewerModelEvent e) {
        switch (e.getReason()) {
        	case ViewerModelEvent.IMAGE_REPAINT:
        		//tree.setModel(new ASTModel(model.getRootNode()));
        		if (model.getImagePath() != null) {
        			System.out.println("OPEN : ".concat(model.getImagePath()));
        			this.openImage(model.getImagePath());
        		}
            break;
            //liuli 2010.4.13 在面板上显示调用图
        	case ViewerModelEvent.IMAGE_CG_REPAINT:
        		if (model.getImagePath() != null) {
        			System.out.println("OPEN : ".concat(model.getImagePath()));
        			this.openImage(model.getImagePath());
        		}
            break;
        }
    }

    /**
     * @see javax.swing.event.TreeSelectionListener#valueChanged(javax.swing.event.TreeSelectionEvent)
     */
    /*
    public void valueChanged(TreeSelectionEvent e) {
        if (e.getNewLeadSelectionPath()!=null)
        model.selectNode((SimpleNode) e.getNewLeadSelectionPath().getLastPathComponent(), this);
    }
    */
}