module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExact
public import StacksFrontier.AlgebraicGeometry.DeRham.UnipotentExteriorPowerModStep
public import StacksFrontier.Data.Nat.AntidiagonalFinite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AbelianOfSmallSite
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFormsSplittingDependence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The graded pieces of the wedge filtration of an exterior power: construction

The categorical helpers used throughout, the graded piece `gr^k⋀ⁿH` of the wedge filtration as
the image of `⋀^kF ⊗ ⋀^{1+m}H` in `⋀ⁿH/F^{k+1}⋀ⁿH`, the fact that the canonical morphism onto
it kills the first step of the second factor, the splitting-free descent through that quotient,
and multiplication by a degree-one generator as a wedge morphism. The module documentation of
`StacksFrontier.AlgebraicGeometry.DeRham.ExteriorGradedPiece` describes the whole development.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

/-! The monoidal structure and the abelian structure are the ones the inputs of this file are
stated at; their names are reused rather than restated so that `⊗`, `◁`, the cokernel and the
image subobject below are the very ones
`StacksFrontier.AlgebraicGeometry.DeRham.UnipotentExteriorPowerModStep` speaks about. -/
attribute [local instance] SheafOfModules.monoidalSheaves
attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite

/-! Both of those are indexed by `CategoryTheory.Sheaf.toRingCat`, while the objects
`Stacks.SheafOfModules.Tensor.sheafTensor` produces are indexed by
`Stacks.SheafOfModules.Tensor.ringSheaf`. The two are the same bundled sheaf of rings, but
`ringSheaf` is an opaque `def`, so a wedge-product morphism out of a `sheafTensor` object is not
recognised as living in the abelian structure just pinned, and `HasImage` cannot be found for it.
Making `ringSheaf` reducible for implicit-argument unification identifies the two spellings at no
further cost. -/
attribute [local instance_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

universe u

namespace Stacks.CategoryTheory

/-- **A transport of the target cancels against its inverse under any functor.** For `E : R = W`
the composite `G(a ≫ b ≫ eqToHom E) ≫ G(eqToHom E.symm) ≫ τ` is `G(a) ≫ G(b) ≫ τ`. This is
stated at generic objects on purpose: at the concrete objects of the wedge filtration the two
spellings of the tensor product make the same statement fail the type-correctness check `rw`
performs, while here there is nothing to unfold. -/
theorem map_comp_eqToHom_comp_map_eqToHom_symm_comp {C₁ : Type*} [_root_.CategoryTheory.Category C₁]
    {D₁ : Type*} [_root_.CategoryTheory.Category D₁] (G : C₁ ⥤ D₁) {P Q R W : C₁} (a : P ⟶ Q)
    (b : Q ⟶ R) (E : R = W) {Y : D₁} (τ : G.obj R ⟶ Y) :
    G.map (a ≫ b ≫ eqToHom E) ≫ G.map (eqToHom E.symm) ≫ τ = G.map a ≫ G.map b ≫ τ := by
  subst E
  simp

/-- **The image of an identity under a bifunctor, evaluated at an object, is the identity.** For
`T : C₁ ⥤ D₁ ⥤ E₁` the component `(T.map (𝟙 X)).app Y` is `𝟙 ((T.obj X).obj Y)`.

Stated at generic objects on purpose, and for the same reason as the transport law above. At the
concrete objects of the wedge filtration the identity that
`CategoryTheory.Functor.map_id` produces lands in the spelling of the ring sheaf that the tensor
product is indexed by, while the identity the goal already carries lands in the other, so neither
`rw` nor `simp only` can key on it and term application cannot unify it either; here `T` is a
variable and there is nothing to unfold. -/
theorem map_id_app {C₁ : Type*} [_root_.CategoryTheory.Category C₁]
    {D₁ : Type*} [_root_.CategoryTheory.Category D₁]
    {E₁ : Type*} [_root_.CategoryTheory.Category E₁] (T : C₁ ⥤ D₁ ⥤ E₁) (X : C₁) (Y : D₁) :
    (T.map (𝟙 X)).app Y = 𝟙 ((T.obj X).obj Y) := by
  rw [T.map_id]
  rfl

/-- **A morphism is an epimorphism as soon as some composite into it is one.** If
`a ≫ b = c ≫ d` with `c` and `d` epimorphisms, then `b` is an epimorphism. Stated at generic
objects on purpose: there is exactly one category instance in scope here, while at the concrete
objects of the wedge filtration the two spellings of the tensor product put two of them there and
instance search picks the wrong one. -/
@[sga "3 IV 1.4" "more general"]
theorem epi_of_comp_eq_epi_comp {C₁ : Type*} [_root_.CategoryTheory.Category C₁]
    {P Q R W : C₁} (a : P ⟶ Q) (b : Q ⟶ R) (c : P ⟶ W) (d : W ⟶ R) (h : a ≫ b = c ≫ d)
    (hc : Epi c) (hd : Epi d) : Epi b := by
  have := hc
  have := hd
  have : Epi (a ≫ b) := Eq.mpr (congrArg Epi h) (epi_comp c d)
  exact epi_of_epi a b

/-- **The image of a transport under a functor is an epimorphism.** Stated at generic objects for
the same reason as `Stacks.CategoryTheory.epi_of_comp_eq_epi_comp`. -/
theorem epi_map_eqToHom {C₁ : Type*} [_root_.CategoryTheory.Category C₁] {D₁ : Type*}
    [_root_.CategoryTheory.Category D₁] (G : C₁ ⥤ D₁) {P Q : C₁} (E : P = Q) :
    Epi (G.map (eqToHom E)) := by
  subst E
  simp only [eqToHom_refl]
  infer_instance

/-- **A morphism is recovered from a one-sided inverse of what it is defined against.** If
`a ≫ b = 𝟙` and `G(b) ≫ c = G(d) ≫ τ`, then `c = G(a ≫ d) ≫ τ`: a morphism characterized by
precomposition with `G(b)` is computed by precomposing the characterizing equation with `G(a)`.
Stated at generic objects for the same reason as the two lemmas above. -/
theorem eq_map_comp_of_section {C₁ : Type*} [_root_.CategoryTheory.Category C₁] {D₁ : Type*}
    [_root_.CategoryTheory.Category D₁] (G : C₁ ⥤ D₁) {P Q R : C₁} {Y : D₁} (a : P ⟶ Q)
    (b : Q ⟶ P) (hab : a ≫ b = 𝟙 P) (c : G.obj P ⟶ Y) (d : Q ⟶ R) (τ : G.obj R ⟶ Y)
    (h : G.map b ≫ c = G.map d ≫ τ) : c = G.map (a ≫ d) ≫ τ := by
  rw [G.map_comp, Category.assoc, ← h, ← Category.assoc, ← G.map_comp, hab, G.map_id,
    Category.id_comp]

/-- **A morphism that factors has a smaller image.** Stated at generic objects for the same
reason as the lemmas above: `exteriorImageFiltration` is elaborated against the abelian structure
`StacksFrontier.AlgebraicGeometry.DeRham.ExteriorPowerFiltration` names and this file against the
one `StacksFrontier.AlgebraicGeometry.DeRham.UnipotentExteriorPowerModFirstStep` names, and
combining a subobject statement from the first with an image lemma synthesized against the second
leaves `HasImage` unsynthesizable. -/
theorem imageSubobject_le_imageSubobject_of_eq_comp {C₁ : Type*}
    [_root_.CategoryTheory.Category C₁] [_root_.CategoryTheory.Abelian C₁] {P Q R : C₁}
    (c : P ⟶ R) (a : P ⟶ Q) (b : Q ⟶ R) (h : c = a ≫ b) :
    imageSubobject c ≤ imageSubobject b := by
  subst h
  exact imageSubobject_comp_le a b

/-- **Cancelling a transport of the target against its inverse.** For `E : S = W` the composite
`(a ≫ b ≫ c ≫ eqToHom E) ≫ eqToHom E.symm ≫ τ` is `a ≫ b ≫ c ≫ τ`. Stated at generic objects
for the same reason as the lemmas above: this is the shape in which the associativity square of
the wedge product, whose second leg ends in a transport of the total degree, is composed with a
morphism out of the untransported degree. -/
theorem comp_comp_comp_eqToHom_comp_eqToHom_symm_comp {C₁ : Type*}
    [_root_.CategoryTheory.Category C₁] {P Q R S W Y : C₁} (a : P ⟶ Q) (b : Q ⟶ R) (c : R ⟶ S)
    (E : S = W) (τ : S ⟶ Y) :
    (a ≫ b ≫ c ≫ eqToHom E) ≫ eqToHom E.symm ≫ τ = a ≫ b ≫ c ≫ τ := by
  subst E
  simp

/-- **A morphism killed after an isomorphism is zero.** Stated at generic objects for the same
reason as the lemmas above. -/
theorem eq_zero_of_iso_comp_eq_zero {C₁ : Type*} [_root_.CategoryTheory.Category C₁]
    [Limits.HasZeroMorphisms C₁] {P Q Y : C₁} (e : P ≅ Q) (θ : Q ⟶ Y) (h : e.hom ≫ θ = 0) :
    θ = 0 :=
  (Iso.inv_hom_id_assoc e θ).symm.trans ((congrArg (fun z => e.inv ≫ z) h).trans comp_zero)

/-- **Whiskering a transport on the left is a monomorphism.** Stated at generic objects: at the
concrete objects of the wedge filtration the two spellings of the tensor product make instance
search for `Mono` pick the wrong category instance. -/
theorem mono_whiskerLeft_eqToHom {C₁ : Type*} [_root_.CategoryTheory.Category C₁]
    [MonoidalCategory C₁] (Z : C₁) {P Q : C₁} (E : P = Q) :
    Mono (MonoidalCategory.whiskerLeft Z (eqToHom E)) := by
  subst E
  simp only [eqToHom_refl, MonoidalCategory.whiskerLeft_id]
  infer_instance

/-- **A morphism with a right inverse is a monomorphism.** Stated at generic objects for the same
reason as the lemmas above, and proved rather than taken from `CategoryTheory.IsSplitMono` so
that no instance has to be synthesized at the concrete objects of the wedge filtration. -/
theorem mono_of_comp_eq_id {C₁ : Type*} [_root_.CategoryTheory.Category C₁] {P Q : C₁}
    (f : P ⟶ Q) (g : Q ⟶ P) (h : f ≫ g = 𝟙 P) : Mono f :=
  ⟨fun a b hab => by
    have h1 : a ≫ f ≫ g = b ≫ f ≫ g :=
      (Category.assoc a f g).symm.trans
        ((congrArg (fun z => z ≫ g) hab).trans (Category.assoc b f g))
    rw [h, Category.comp_id, Category.comp_id] at h1
    exact h1⟩

/-- **A monomorphism precomposed with a monomorphism is one.** Stated at generic objects for the
same reason as the lemmas above: at the concrete objects there are two category instances in
scope and instance search picks the wrong one. -/
theorem mono_comp_of_mono {C₁ : Type*} [_root_.CategoryTheory.Category C₁] {P Q R : C₁}
    (f : P ⟶ Q) (g : Q ⟶ R) (hf : Mono f) (hg : Mono g) : Mono (f ≫ g) :=
  have := hf
  have := hg
  mono_comp f g

end Stacks.CategoryTheory

namespace SheafOfModules

open MonoidalCategory

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {F G H : SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (AF : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) F)
  (AG : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) G)
  (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) H)

/-! ### The graded piece -/

/-- **The canonical morphism `⋀^kF ⊗ ⋀^{1+m}H ⟶ ⋀ⁿH/F^{k+1}⋀ⁿH`**, `n = k + 1 + m`: the
wedge-product morphism onto `⋀ⁿH`, whose image is the `k`-th step `F^k⋀ⁿH` of the wedge
filtration, followed by the projection onto the quotient by the `(k+1)`-st step. -/
def exteriorGradedHom (iF : F ⟶ H) (k m : ℕ) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        Osharp)).obj (AF.exteriorPower k, A.exteriorPower (1 + m)) ⟶
      cokernel (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m) :=
  prodWedgeHom AF A A iF (𝟙 H) k (1 + m) ≫
    eqToHom (congrArg A.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm) ≫
      cokernel.π (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m)

/-- **`gr^k⋀ⁿH`**, the `k`-th graded piece of the wedge filtration of `⋀ⁿH` for the total degree
`n = k + 1 + m`: the image of `SheafOfModules.exteriorGradedHom`, i.e. the image of the `k`-th
step `F^k⋀ⁿH` of the filtration inside the quotient `⋀ⁿH/F^{k+1}⋀ⁿH`.

That this is `F^k⋀ⁿH/F^{k+1}⋀ⁿH` is `SheafOfModules.imageSubobject_exteriorGradedHom_eq`. -/
abbrev exteriorGraded (iF : F ⟶ H) (k m : ℕ) :
    SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp) :=
  ((imageSubobject (exteriorGradedHom AF A iF k m) :
    SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp)))

/-- **The canonical morphism `⋀^kF ⊗ ⋀^{1+m}H ⟶ gr^k⋀ⁿH` onto the graded piece**: the
factorization of `SheafOfModules.exteriorGradedHom` through its image. -/
abbrev toExteriorGraded (iF : F ⟶ H) (k m : ℕ) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        Osharp)).obj (AF.exteriorPower k, A.exteriorPower (1 + m)) ⟶
      exteriorGraded AF A iF k m :=
  factorThruImageSubobject (exteriorGradedHom AF A iF k m)

/-- **The canonical morphism onto the graded piece is an epimorphism.** -/
theorem epi_toExteriorGraded (iF : F ⟶ H) (k m : ℕ) : Epi (toExteriorGraded AF A iF k m) :=
  Stacks.CategoryTheory.Subobject.epi_factorThruImageSubobject _

/-- The canonical morphism onto the graded piece, followed by the inclusion of the graded piece
into `⋀ⁿH/F^{k+1}⋀ⁿH`, is `SheafOfModules.exteriorGradedHom`. -/
@[reassoc]
theorem toExteriorGraded_comp_arrow (iF : F ⟶ H) (k m : ℕ) :
    toExteriorGraded AF A iF k m ≫ (imageSubobject (exteriorGradedHom AF A iF k m)).arrow =
      exteriorGradedHom AF A iF k m :=
  imageSubobject_arrow_comp _

/-- **The graded piece is `F^k⋀ⁿH/F^{k+1}⋀ⁿH`**: the image of
`SheafOfModules.exteriorGradedHom` is the image of the `k`-th step of the wedge filtration of
`⋀ⁿH` inside the quotient by the `(k+1)`-st step.

The two differ by precomposition with the epimorphism of the `k`-th step onto its image, which
does not change an image (`Stacks.CategoryTheory.Subobject.imageSubobject_epi_comp`). -/
theorem imageSubobject_exteriorGradedHom_eq (iF : F ⟶ H) (k m : ℕ) :
    imageSubobject (exteriorGradedHom AF A iF k m) =
      imageSubobject ((imageSubobject (prodWedgeHom AF A A iF (𝟙 H) k (1 + m) ≫
            eqToHom (congrArg A.exterior.piece
              (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm))).arrow ≫
        cokernel.π (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m)) := by
  have key : factorThruImageSubobject (prodWedgeHom AF A A iF (𝟙 H) k (1 + m) ≫
          eqToHom (congrArg A.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm)) ≫
        ((imageSubobject (prodWedgeHom AF A A iF (𝟙 H) k (1 + m) ≫
            eqToHom (congrArg A.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm))).arrow ≫
          cokernel.π (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m)) =
      exteriorGradedHom AF A iF k m := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg
      (fun z => z ≫ cokernel.π (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m))
      (imageSubobject_arrow_comp (prodWedgeHom AF A A iF (𝟙 H) k (1 + m) ≫
        eqToHom (congrArg A.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm)))) ?_
    exact Category.assoc _ _ _
  rw [← key]
  exact Stacks.CategoryTheory.Subobject.imageSubobject_epi_comp _
    (Stacks.CategoryTheory.Subobject.epi_factorThruImageSubobject _) _

/-- Two spellings of the complementary degree give the same step of the wedge filtration. -/
theorem imageSubobject_prodWedgeHomOfEq_congr (iF : F ⟶ H) (k q q' n : ℕ) (h : k + q = n)
    (h' : k + q' = n) (hq : q = q') :
    imageSubobject (prodWedgeHomOfEq AF A A iF (𝟙 H) k q n h) =
      imageSubobject (prodWedgeHomOfEq AF A A iF (𝟙 H) k q' n h') := by
  subst hq
  rfl

/-- The step of `SheafOfModules.exteriorImageFiltration` with the complementary degree named by a
hypothesis rather than written as a subtraction: for `k + q = n` the `k`-th step of the wedge
filtration of `⋀ⁿH` is the image of `⋀^kF ⊗ ⋀^qH ⟶ ⋀ⁿH`. At `q = 1 + m` this is the step the
graded piece above is built from. -/
theorem exteriorImageFiltration_eq_imageSubobject (iF : F ⟶ H) (k q n : ℕ) (h : k + q = n) :
    exteriorImageFiltration AF A iF n k =
      imageSubobject (prodWedgeHomOfEq AF A A iF (𝟙 H) k q n h) := by
  rw [exteriorImageFiltration_of_le AF A iF n k (by omega)]
  exact imageSubobject_prodWedgeHomOfEq_congr AF A iF k (n - k) q n _ h (by omega)

/-! ### The first step of the second factor is killed -/

/-- **The canonical morphism onto `gr^k⋀ⁿH` kills `⋀^kF ⊗ F^1⋀^{1+m}H`**, before factoring
through the image. Wedging the first step of the wedge filtration of `⋀^{1+m}H` with `⋀^kF` lands
in the `(k+1)`-st step of the wedge filtration of `⋀ⁿH`
(`SheafOfModules.whiskerLeft_prodWedgeHom_comp_prodWedgeHom_comp_cokernelπ`), which is exactly
what the quotient divides out. -/
theorem whiskerLeft_prodWedgeHom_comp_exteriorGradedHom (iF : F ⟶ H) (k m : ℕ) :
    (AF.exteriorPower k ◁ prodWedgeHom AF A A iF (𝟙 H) 1 m) ≫ exteriorGradedHom AF A iF k m =
      0 :=
  whiskerLeft_prodWedgeHom_comp_prodWedgeHom_comp_cokernelπ AF A iF k m

/-- **The canonical morphism onto `gr^k⋀ⁿH` kills `⋀^kF ⊗ F^1⋀^{1+m}H`**: it depends on its
second factor only modulo the first step of the wedge filtration of `⋀^{1+m}H`, i.e. only
through the quotient of `⋀^{1+m}H` by the forms coming from `F`. -/
theorem whiskerLeft_prodWedgeHom_comp_toExteriorGraded (iF : F ⟶ H) (k m : ℕ) :
    (AF.exteriorPower k ◁ prodWedgeHom AF A A iF (𝟙 H) 1 m) ≫ toExteriorGraded AF A iF k m =
      0 := by
  refine (cancel_mono (imageSubobject (exteriorGradedHom AF A iF k m)).arrow).1 ?_
  refine Eq.trans (Category.assoc _ _ _) (Eq.trans ?_ zero_comp.symm)
  refine Eq.trans (congrArg
    (fun z => (AF.exteriorPower k ◁ prodWedgeHom AF A A iF (𝟙 H) 1 m) ≫ z)
    (toExteriorGraded_comp_arrow AF A iF k m)) ?_
  exact whiskerLeft_prodWedgeHom_comp_exteriorGradedHom AF A iF k m

/-! ### The splitting-free comparison out of the quotient by the first step -/

/-- `SheafOfModules.whiskerLeft_prodWedgeHom_comp_toExteriorGraded` in the functor spelling: the
canonical morphism onto the graded piece kills `⋀^kF` tensored with the first step of the wedge
filtration of `⋀^{1+m}H`. The functor is `Stacks.SheafOfModules.Tensor.sheafTensor` evaluated at
`⋀^kF`, i.e. tensoring on the left with `⋀^kF`, whose preservation of zero morphisms and of the
colimit of a parallel pair are the instances the descent below needs. -/
theorem tensorLeftFunctor_map_prodWedgeHom_comp_toExteriorGraded (iF : F ⟶ H) (k m : ℕ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (AF.exteriorPower k)).map
        (prodWedgeHom AF A A iF (𝟙 H) 1 m) ≫
      toExteriorGraded AF A iF k m = 0 := by
  have hbr : ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (AF.exteriorPower k)).map
        (prodWedgeHom AF A A iF (𝟙 H) 1 m) =
      AF.exteriorPower k ◁ prodWedgeHom AF A A iF (𝟙 H) 1 m := by
    rw [Stacks.SheafOfModules.Strict.whiskerLeft_eq_tensorSheafBifunctor_map Osharp
      (AF.exteriorPower k) (prodWedgeHom AF A A iF (𝟙 H) 1 m),
      Stacks.CategoryTheory.map_id_app, Category.id_comp]
  exact Eq.trans (congrArg (fun z => z ≫ toExteriorGraded AF A iF k m) hbr)
    (whiskerLeft_prodWedgeHom_comp_toExteriorGraded AF A iF k m)

/-- **The canonical splitting-free comparison onto the graded piece**:

`⋀^kF ⊗ (⋀^{1+m}H/F^1⋀^{1+m}H) ⟶ gr^k⋀ⁿH`,  `n = k + 1 + m`.

No splitting enters, and nothing is assumed. The canonical morphism
`⋀^kF ⊗ ⋀^{1+m}H ↠ gr^k⋀ⁿH` kills `⋀^kF` tensored with the first step `F^1⋀^{1+m}H` of the
wedge filtration of the second factor
(`SheafOfModules.whiskerLeft_prodWedgeHom_comp_toExteriorGraded`), and tensoring with `⋀^kF`
preserves the cokernel of the inclusion of that first step, because the tensor product of
sheaves of modules preserves all colimits in each variable ([Stacks, Tag 05NB]). So the morphism
descends, uniquely, to the quotient.

Once `⋀^{1+m}H/F^1⋀^{1+m}H` is identified with `⋀^{1+m}(H/F)` — which for a short exact sequence
`0 ⟶ F ⟶ H ⟶ H/F ⟶ 0` is [Stacks, Tag 01CJ],
`SheafOfModules.ExtPresentation.exteriorPresentation_exact` — this is the glued comparison

`⋀^kF ⊗ ⋀^{1+m}(H/F) ⟶ gr^k⋀ⁿH`

of [Stacks, Section 0FMK], and `SheafOfModules.splittingToExteriorGraded_eq` says the local
Künneth comparisons all factor through it. -/
noncomputable def exteriorGradedDescent (iF : F ⟶ H) (k m : ℕ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (AF.exteriorPower k)).obj
        (cokernel (prodWedgeHom AF A A iF (𝟙 H) 1 m)) ⟶
      exteriorGraded AF A iF k m :=
  (isColimitOfHasCokernelOfPreservesColimit
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (AF.exteriorPower k))
      (prodWedgeHom AF A A iF (𝟙 H) 1 m)).desc
    (CokernelCofork.ofπ (toExteriorGraded AF A iF k m)
      (tensorLeftFunctor_map_prodWedgeHom_comp_toExteriorGraded AF A iF k m))

/-- **The defining equation of the splitting-free comparison**: precomposed with `⋀^kF` tensored
with the projection of `⋀^{1+m}H` onto its quotient by the first step of the wedge filtration, it
is the canonical morphism onto the graded piece. That projection becomes an epimorphism after
tensoring with `⋀^kF`, so this equation determines
`SheafOfModules.exteriorGradedDescent`. -/
theorem tensorLeftFunctor_map_cokernelπ_comp_exteriorGradedDescent (iF : F ⟶ H) (k m : ℕ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (AF.exteriorPower k)).map
          (cokernel.π (prodWedgeHom AF A A iF (𝟙 H) 1 m)) ≫
        exteriorGradedDescent AF A iF k m =
      toExteriorGraded AF A iF k m :=
  Cofork.IsColimit.π_desc
    (isColimitOfHasCokernelOfPreservesColimit
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (AF.exteriorPower k))
      (prodWedgeHom AF A A iF (𝟙 H) 1 m))

/-- **The canonical morphism onto `gr^k` kills the wedge morphism out of `⋀^1F ⊗ ⋀^mH`, after
any transport of the total degree and tensoring with `⋀^kF`.** The degree-one generator in the
first factor and the transport `E` are both harmless: the transport cancels against its inverse,
and what remains is
`SheafOfModules.tensorLeftFunctor_map_prodWedgeHom_comp_toExteriorGraded`. This is the form in
which the relation of the presentation of [Stacks, Tag 01CJ] is killed. -/
theorem tensorLeftFunctor_map_generatorTensorId_comp_toExteriorGraded (iF : F ⟶ H) (k m : ℕ)
    {W : SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (E : A.exteriorPower (1 + m) = W) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (AF.exteriorPower k)).map
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
              ((AF.exteriorGenerator, 𝟙 (A.exteriorPower m)) :
                (F, A.exteriorPower m) ⟶ (AF.exteriorPower 1, A.exteriorPower m)) ≫
            prodWedgeHom AF A A iF (𝟙 H) 1 m ≫ eqToHom E) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj
              (AF.exteriorPower k)).map (eqToHom E.symm) ≫
          toExteriorGraded AF A iF k m =
      0 :=
  Eq.trans
    (Stacks.CategoryTheory.map_comp_eqToHom_comp_map_eqToHom_symm_comp
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (AF.exteriorPower k))
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
          ((AF.exteriorGenerator, 𝟙 (A.exteriorPower m)) :
            (F, A.exteriorPower m) ⟶ (AF.exteriorPower 1, A.exteriorPower m)))
      (prodWedgeHom AF A A iF (𝟙 H) 1 m) E (toExteriorGraded AF A iF k m))
    (Eq.trans
      (congrArg (fun z => ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj
              (AF.exteriorPower k)).map
            ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
                ((AF.exteriorGenerator, 𝟙 (A.exteriorPower m)) :
                  (F, A.exteriorPower m) ⟶ (AF.exteriorPower 1, A.exteriorPower m))) ≫ z)
        (tensorLeftFunctor_map_prodWedgeHom_comp_toExteriorGraded AF A iF k m))
      comp_zero)

/-- `SheafOfModules.prodWedgeHom_eq_whiskerLeft_pieceMap_comp`, transported along `p + q = n`. -/
theorem prodWedgeHomOfEq_eq_whiskerLeft_pieceMap_comp (iF : F ⟶ H) (iG : G ⟶ H) (p q n : ℕ)
    (h : p + q = n) :
    prodWedgeHomOfEq AF AG A iF iG p q n h =
      (AF.exteriorPower p ◁
          AG.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iG (q : ℤ)) ≫
        prodWedgeHomOfEq AF A A iF (𝟙 H) p q n h :=
  Eq.trans
    (congrArg (fun z => z ≫ eqToHom (congrArg (fun j : ℕ => A.exteriorPower j) h))
      (prodWedgeHom_eq_whiskerLeft_pieceMap_comp AF AG A iF iG p q))
    (Category.assoc _ _ _)

/-- **The Künneth summand of weight `p` lands in the `p`-th step of the wedge filtration.** The
summand `⋀^pF ⊗ ⋀^qG` of the Künneth decomposition of `⋀ⁿH` along a splitting maps into `⋀ⁿH` by
the wedge-product morphism along the inclusion of the sub and the section of the quotient, and
that morphism factors through the wedge-product morphism out of `⋀^pF ⊗ ⋀^qH`, whose image is the
`p`-th step `F^p⋀ⁿH` of the wedge filtration —
`SheafOfModules.exteriorImageFiltration_eq_imageSubobject` is that identification, kept separate
because the two sides are elaborated against two different abelian structures.

This is one of the two inclusions of the weight-matching the injectivity of
`SheafOfModules.exteriorGradedQuotientComparison` needs; the other is the retraction
`SheafOfModules.exteriorKunnethRetraction` killing every summand of higher weight. -/
theorem imageSubobject_prodWedgeHomOfEq_splitting_le (iF : F ⟶ H) (iG : G ⟶ H) (p q n : ℕ)
    (h : p + q = n) :
    imageSubobject (prodWedgeHomOfEq AF AG A iF iG p q n h) ≤
      imageSubobject (prodWedgeHomOfEq AF A A iF (𝟙 H) p q n h) :=
  Stacks.CategoryTheory.imageSubobject_le_imageSubobject_of_eq_comp _ _ _
    (prodWedgeHomOfEq_eq_whiskerLeft_pieceMap_comp AF AG A iF iG p q n h)

/-- **The Künneth comparison along a map `iG : G ⟶ H`, composed into `⋀ⁿH/F^{k+1}⋀ⁿH`.**
Precomposing `SheafOfModules.exteriorGradedHom` with `⋀^{1+m}iG` in the second factor is the
wedge-product morphism out of `⋀^kF ⊗ ⋀^{1+m}G`, projected to the quotient by the next step. -/
theorem whiskerLeft_pieceMap_comp_exteriorGradedHom (iF : F ⟶ H) (iG : G ⟶ H) (k m : ℕ) :
    (AF.exteriorPower k ◁
          AG.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iG
            ((1 + m : ℕ) : ℤ)) ≫
        exteriorGradedHom AF A iF k m =
      prodWedgeHom AF AG A iF iG k (1 + m) ≫
        eqToHom (congrArg A.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm) ≫
          cokernel.π (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m) := by
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg (fun z => z ≫
      eqToHom (congrArg A.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm) ≫
        cokernel.π (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m))
    (prodWedgeHom_eq_whiskerLeft_pieceMap_comp AF AG A iF iG k (1 + m)).symm

/-! ### Multiplication by a degree-one generator is a wedge morphism -/

namespace GradedAlgebra

/-- **Multiplication by a degree-one generator is the tensor product with that generator followed
by the multiplication of the graded algebra**: `M ⊗ A_k ⟶ A_1 ⊗ A_k ⟶ A_{1+k}`. Both morphisms
take a pure tensor `s ⊗ y` to `ι(s)·y`, the second factor being untouched. -/
theorem generatorMul_eq_tensorSheafBifunctor_map_comp_mulSheaf
    {M : SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (B : GradedAlgebra.{u, u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp))
    (ι : M ⟶ B.piece 1) (k : ℤ) :
    generatorMul ι k =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
          ((ι, 𝟙 (B.piece k)) : (M, B.piece k) ⟶ (B.piece 1, B.piece k)) ≫
        mulSheaf B 1 k := by
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := Osharp) fun U s y => ?_
  refine Eq.trans (generatorMul_unit ι k U s y) ?_
  refine Eq.trans ?_ (comp_val_app_apply _ _ U _).symm
  refine Eq.trans ?_ (congrArg ((mulSheaf B 1 k).val.app U)
    (Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit Osharp
      M (B.piece k) ι (𝟙 (B.piece k)) U s y)).symm
  refine Eq.trans ?_ (mulSheaf_unit B 1 k U _ _).symm
  simp

end GradedAlgebra

/-- The wedge-product morphism `⋀^1F ⊗ ⋀^mH ⟶ ⋀^{1+m}H`, unfolded: the map induced on the
exterior powers by `iF` and by `𝟙 H`, followed by the multiplication of the exterior algebra of
`H`. This is `SheafOfModules.prodWedgeHom` by definition; it is named so that the two spellings
`(1 : ℤ)` and `((1 : ℕ) : ℤ)` of the degree-one index are reconciled once, in a declaration of
its own. -/
theorem prodWedgeHom_one_left_eq (iF : F ⟶ H) (m : ℕ) :
    prodWedgeHom AF A A iF (𝟙 H) 1 m =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
          ((AF.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iF 1,
              A.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra (𝟙 H) (m : ℤ)) :
            (AF.exteriorPower 1, A.exteriorPower m) ⟶
              (A.exterior.piece 1, A.exterior.piece (m : ℤ))) ≫
        GradedAlgebra.mulSheaf A.exterior 1 (m : ℤ) :=
  rfl

/-- **The degree-one generator intertwines the two left factors.** Tensoring with the degree-one
generator of the exterior algebra of `F` and then with the map `⋀^1F ⟶ ⋀^1H` induced by `iF` is
tensoring with `iF` followed by the degree-one generator of the exterior algebra of `H`: in
degree one the comparison of exterior algebras carries one generator to the other
(`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.map_app_one`), and the second factor is
untouched because the map induced by `𝟙 H` is the identity. -/
theorem generatorTensorId_comp_pieceMapTensorPieceMap (iF : F ⟶ H) (m : ℕ) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
          ((AF.exteriorGenerator, 𝟙 (A.exteriorPower m)) :
            (F, A.exteriorPower m) ⟶ (AF.exteriorPower 1, A.exteriorPower m)) ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
          ((AF.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iF 1,
              A.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra (𝟙 H) (m : ℤ)) :
            (AF.exteriorPower 1, A.exteriorPower m) ⟶
              (A.exterior.piece 1, A.exterior.piece (m : ℤ))) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
        ((iF ≫ A.exteriorGenerator, 𝟙 (A.exteriorPower m)) :
          (F, A.exteriorPower m) ⟶ (A.exterior.piece 1, A.exterior.piece (m : ℤ))) := by
  rw [← Functor.map_comp]
  congr 1
  refine Prod.ext ?_ ?_
  · exact AF.exterior_isExteriorAlgebra.map_app_one A.exterior_isExteriorAlgebra iF
  · rw [A.exterior_isExteriorAlgebra.pieceMap_id (m : ℤ)]
    exact Category.comp_id _

/-- **The first morphism of the presentation of [Stacks, Tag 01CJ] is the wedge morphism.**
Multiplication by the degree-one image of `F`, i.e. `F ⊗ ⋀^mH ⟶ ⋀^{1+m}H`, is the wedge-product
morphism `⋀^1F ⊗ ⋀^mH ⟶ ⋀^{1+m}H` precomposed with the degree-one generator of the exterior
algebra of `F` in the first factor.

The degree-one generator is invertible
(`SheafOfModules.TensorExteriorSymmetricAlgebras.isIso_exteriorGenerator`), so the two morphisms
have the same cokernel; for a short exact sequence `0 ⟶ F ⟶ H ⟶ H/F ⟶ 0` Tag 01CJ identifies
that cokernel with `⋀^{1+m}(H/F)`, which is how the source of
`SheafOfModules.exteriorGradedDescent` acquires the shape [Stacks, Section 0FMK] states. -/
theorem generatorMul_eq_generatorTensorId_comp_prodWedgeHom (iF : F ⟶ H) (m : ℕ) :
    GradedAlgebra.generatorMul (iF ≫ A.exteriorGenerator) (m : ℤ) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
          ((AF.exteriorGenerator, 𝟙 (A.exteriorPower m)) :
            (F, A.exteriorPower m) ⟶ (AF.exteriorPower 1, A.exteriorPower m)) ≫
        prodWedgeHom AF A A iF (𝟙 H) 1 m := by
  refine Eq.trans (GradedAlgebra.generatorMul_eq_tensorSheafBifunctor_map_comp_mulSheaf
    A.exterior (iF ≫ A.exteriorGenerator) (m : ℤ)) ?_
  refine Eq.trans (congrArg (fun z => z ≫ GradedAlgebra.mulSheaf A.exterior 1 (m : ℤ))
    (generatorTensorId_comp_pieceMapTensorPieceMap AF A iF m).symm) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact congrArg
    (fun z => (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp)).map
        ((AF.exteriorGenerator, 𝟙 (A.exteriorPower m)) :
          (F, A.exteriorPower m) ⟶ (AF.exteriorPower 1, A.exteriorPower m)) ≫ z)
    (prodWedgeHom_one_left_eq AF A iF m).symm

end SheafOfModules

end
