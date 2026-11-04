module

public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.AlgebraicGeometry.Sites.Representability
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.RepresentedBy
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.FreeOnAffineOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Representability
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.RelativeMorphisms
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.BootstrapEtaleSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartComparisonAssembly
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Stability
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RelativeMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RelativeMorphismsFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Diagonal
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeHomRepresentableAffineTarget.HomEquivalences
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeHomRepresentableAffineTarget.SliceRepresentability

/-!
# The relative morphism functor of a coproduct-of-affines target is an algebraic space

The identification of the relative morphism functor on the slice with the functor of Stacks 05Y2,
the case of Stacks 05Y7 in which everything is an object of the site, and Stacks 05Y7 for arbitrary
algebraic spaces by base change to a representable base.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u v w u'

namespace AlgebraicGeometry.RelativeHomAffineTarget

open MonoidalCategory CartesianMonoidalCategory

open TopologicalSpace

/-! ### From the slice to the relative morphism functor of Stacks 05Y2 -/

/-- **A pair of Stacks 05Y1 at a representable test object is a pair of morphisms of the site.**
Both components are transported by full faithfulness of Yoneda: the first directly, the second
through the identification of the base change `T ×_{a, Q} Z` computed in the site with the one
computed in presheaves. -/
private noncomputable def relativeMorphismYonedaEquiv
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T Z X Q : BigFppfOver B S hS} (z : Z ⟶ Q) (x : X ⟶ Q) :
    (Σ a : T ⟶ Q, {b : pullback a z ⟶ X // b ≫ x = pullback.snd a z ≫ z}) ≃
      Space.RelativeMorphism B S hS (yoneda.obj Z) (yoneda.obj X)
        (yoneda.obj Q) (yoneda.map z) (yoneda.map x) (yoneda.obj T) :=
  by
  let e :
      (Σ a : T ⟶ Q, {b : pullback a z ⟶ X // b ≫ x = pullback.snd a z ≫ z}) ≃
      (Σ a : yoneda.obj T ⟶ yoneda.obj Q,
        {b : pullback a (yoneda.map z) ⟶ yoneda.obj X //
          b ≫ yoneda.map x = pullback.snd a (yoneda.map z) ≫ yoneda.map z}) :=
    Equiv.sigmaCongr (Functor.FullyFaithful.ofFullyFaithful yoneda).homEquiv
      (fun a => pullbackHomEquiv yoneda a z x)
  exact e.trans
    { toFun := fun p => ⟨p.1, p.2.val, p.2.property⟩
      invFun := fun p => ⟨p.base, p.morphism, p.commutes⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

attribute [local implicit_reducible] relativeMorphismYonedaEquiv in
/-- The identification of pairs with pairs of morphisms of the site is natural in the test
object: restricting a pair along `t` is precomposing the first component with `t` and base
changing the second. -/
private lemma relativeMorphismYonedaEquiv_natural
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T T' Z X Q : BigFppfOver B S hS} (a : T ⟶ Q) (z : Z ⟶ Q)
    (x : X ⟶ Q) (t : T' ⟶ T) (b : pullback a z ⟶ X)
    (hb : b ≫ x = pullback.snd a z ≫ z) :
    relativeMorphismYonedaEquiv B S hS z x
      ⟨t ≫ a, pullback.map (t ≫ a) z a z t (𝟙 Z) (𝟙 Q) (by simp) (by simp) ≫ b,
        by simp [Category.assoc, hb]⟩ =
      Space.RelativeMorphism.restrict (yoneda.map t)
        (relativeMorphismYonedaEquiv B S hS z x ⟨a, b, hb⟩) := by
  have hbase : yoneda.map (t ≫ a) = yoneda.map t ≫ yoneda.map a := yoneda.map_comp t a
  refine Space.RelativeMorphism.ext_of_base_eq hbase ?_
  change (pullbackHomEquiv yoneda (t ≫ a) z x
      ⟨pullback.map (t ≫ a) z a z t (𝟙 Z) (𝟙 Q) _ _ ≫ b, _⟩).val =
    (pullback.congrHom hbase rfl).hom ≫
      pullback.map (yoneda.map t ≫ yoneda.map a) (yoneda.map z) (yoneda.map a) (yoneda.map z)
        (yoneda.map t) (𝟙 _) (𝟙 _) _ _ ≫
        (pullbackHomEquiv yoneda a z x ⟨b, hb⟩).val
  rw [pullbackHomEquiv_natural yoneda a z x t b hb, ← Category.assoc]
  congr 1
  apply pullback.hom_ext <;>
    simp [pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc]

/-- **The sections of a representing object of the relative morphism functor on the slice are the
pairs of Stacks 05Y1.** A morphism `T ⟶ W.left` is the same as a morphism `Over.mk a ⟶ W` for
`a` its composite with the structure morphism of `W`, hence by representability a `Q`-morphism
out of the product `Over.mk a ⨯ Over.mk z`, hence a pair. -/
private noncomputable def relativeHomSectionsEquivOfRepresentable
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X Q : BigFppfOver B S hS} [HasBinaryProducts (Over Q)]
    (z : Z ⟶ Q) (x : X ⟶ Q) (W : Over Q)
    (r : ((prod.functor.obj (Over.mk z)).op ⋙ yoneda.obj (Over.mk x)).RepresentableBy W)
    (T : BigFppfOver B S hS) :
    (T ⟶ W.left) ≃ Space.RelativeMorphism B S hS
      (yoneda.obj Z) (yoneda.obj X) (yoneda.obj Q)
      (yoneda.map z) (yoneda.map x) (yoneda.obj T) :=
  (sigmaOverHomEquiv W).symm.trans
    ((Equiv.sigmaCongrRight (fun a : T ⟶ Q =>
      r.homEquiv.trans (overProductHomEquiv a z x))).trans
      (relativeMorphismYonedaEquiv B S hS z x))

/-- Naturality of the identification of a `Q`-morphism out of a product with a pair, in the test
object. -/
private lemma relativeMorphismFromOverHom_natural
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T T' Z X Q : BigFppfOver B S hS} [HasBinaryProducts (Over Q)]
    (a : T ⟶ Q) (z : Z ⟶ Q) (x : X ⟶ Q) (t : T' ⟶ T) (W : Over Q)
    (r : ((prod.functor.obj (Over.mk z)).op ⋙ yoneda.obj (Over.mk x)).RepresentableBy W)
    (f : Over.mk a ⟶ W) :
    relativeMorphismYonedaEquiv B S hS z x
      ⟨t ≫ a, overProductHomEquiv (t ≫ a) z x
        (r.homEquiv ((Over.homMk t rfl : Over.mk (t ≫ a) ⟶ Over.mk a) ≫ f))⟩ =
      Space.RelativeMorphism.restrict (yoneda.map t)
        (relativeMorphismYonedaEquiv B S hS z x
          ⟨a, overProductHomEquiv a z x (r.homEquiv f)⟩) := by
  let b := overProductHomEquiv a z x (r.homEquiv f)
  have h : overProductHomEquiv (t ≫ a) z x
      (r.homEquiv ((Over.homMk t rfl : Over.mk (t ≫ a) ⟶ Over.mk a) ≫ f)) =
      ⟨pullback.map (t ≫ a) z a z t (𝟙 Z) (𝟙 Q) (by simp) (by simp) ≫ b.val,
        by simp [Category.assoc, b.property]⟩ := by
    apply Subtype.ext
    rw [r.homEquiv_comp]
    exact overProductHomEquiv_natural a z x t (r.homEquiv f)
  rw [h]
  exact relativeMorphismYonedaEquiv_natural B S hS a z x t b.val b.property

/-- The pair attached to a morphism into a representing object does not depend on which proof of
the factorization through the base is used. -/
private lemma relativeMorphismFromOverHom_congr
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T Z X Q : BigFppfOver B S hS} [HasBinaryProducts (Over Q)]
    (z : Z ⟶ Q) (x : X ⟶ Q) (W : Over Q)
    (r : ((prod.functor.obj (Over.mk z)).op ⋙ yoneda.obj (Over.mk x)).RepresentableBy W)
    {a a' : T ⟶ Q} (h : a = a') (f : T ⟶ W.left)
    (hf : f ≫ W.hom = a) (hf' : f ≫ W.hom = a') :
    relativeMorphismYonedaEquiv B S hS z x
      ⟨a, overProductHomEquiv a z x (r.homEquiv (Over.homMk f hf))⟩ =
    relativeMorphismYonedaEquiv B S hS z x
      ⟨a', overProductHomEquiv a' z x (r.homEquiv (Over.homMk f hf'))⟩ := by
  subst a'
  rfl

/-- The identification of the sections of a representing object with pairs is natural. -/
private lemma relativeHomSectionsEquivOfRepresentable_natural
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T T' Z X Q : BigFppfOver B S hS} [HasBinaryProducts (Over Q)]
    (z : Z ⟶ Q) (x : X ⟶ Q) (W : Over Q)
    (r : ((prod.functor.obj (Over.mk z)).op ⋙ yoneda.obj (Over.mk x)).RepresentableBy W)
    (f : T ⟶ W.left) (t : T' ⟶ T) :
    relativeHomSectionsEquivOfRepresentable B S hS z x W r T' (t ≫ f) =
      Space.RelativeMorphism.restrict (yoneda.map t)
        (relativeHomSectionsEquivOfRepresentable B S hS z x W r T f) := by
  change relativeMorphismYonedaEquiv B S hS z x
      ⟨(t ≫ f) ≫ W.hom, overProductHomEquiv ((t ≫ f) ≫ W.hom) z x
        (r.homEquiv (Over.homMk (t ≫ f) rfl))⟩ =
    Space.RelativeMorphism.restrict (yoneda.map t)
      (relativeMorphismYonedaEquiv B S hS z x
        ⟨f ≫ W.hom, overProductHomEquiv (f ≫ W.hom) z x
          (r.homEquiv (Over.homMk f rfl))⟩)
  refine (relativeMorphismFromOverHom_congr B S hS z x W r
    (Category.assoc t f W.hom) (t ≫ f) rfl (Category.assoc t f W.hom)).trans ?_
  simpa only [← Over.homMk_comp] using
    relativeMorphismFromOverHom_natural B S hS (f ≫ W.hom) z x t W r
      (Over.homMk f rfl)

/-- **A representing object of the relative morphism functor on the slice over `Q` represents the
relative morphism functor of Stacks 05Y2.** The two functors have the same sections, naturally. -/
private noncomputable def relativeHomRepresentableByOfOver
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X Q : BigFppfOver B S hS} [HasBinaryProducts (Over Q)]
    (z : Z ⟶ Q) (x : X ⟶ Q) (W : Over Q)
    (r : ((prod.functor.obj (Over.mk z)).op ⋙ yoneda.obj (Over.mk x)).RepresentableBy W) :
    (Space.relativeHom B S hS (yoneda.obj Z) (yoneda.obj X) (yoneda.obj Q)
      (yoneda.map z) (yoneda.map x)
      (isAlgebraicSpace_yoneda B S hS Z)
      (isAlgebraicSpace_yoneda B S hS X)
      (isAlgebraicSpace_yoneda B S hS Q)).RepresentableBy W.left where
  homEquiv {T} := (relativeHomSectionsEquivOfRepresentable B S hS z x W r T).trans
    (Space.relativeHomSections B S hS (yoneda.obj Z) (yoneda.obj X) (yoneda.obj Q)
      (yoneda.map z) (yoneda.map x) _ _ _ T).symm
  homEquiv_comp {T T'} f g := by
    apply (Space.relativeHomSections B S hS (yoneda.obj Z) (yoneda.obj X)
      (yoneda.obj Q) (yoneda.map z) (yoneda.map x) _ _ _ T).injective
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply,
      Space.relativeHomSections_map]
    exact relativeHomSectionsEquivOfRepresentable_natural B S hS z x W r g f

/-! ### The relative morphism functor of a coproduct-of-affines target -/

/-- **The relative morphism functor of objects of the site, with a coproduct-of-affines target, is
represented by an object of the site.** Representability on the slice of all schemes over the
scheme underlying `Q` is
`AlgebraicGeometry.RelativeHomAffineTarget.relativeHom_representableBy_coproduct_size_le`,
together with the bound on the size of the representing scheme that puts it in the site; the
slice over `Q` in the site is carried there by the fully faithful functor
`Over.post B.inclusion`, and
`AlgebraicGeometry.RelativeHomAffineTarget.relativeHomRepresentableByOfOver` turns a representing
object on that slice into one for the functor of Stacks 05Y2. -/
private lemma isRepresentable_relativeHom_coproduct
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (Z X Q : BigFppfOver B S hS) (z : Z ⟶ Q) (x : X ⟶ Q)
    [(B.inclusion.obj Q.left).IsSeparated]
    [Stacks.Morphisms.IsFiniteLocallyFree (B.inclusion.map z.left)]
    {I : Type u} (Y : I → Scheme.{u}) [∀ i, IsAffine (Y i)]
    (e : (∐ Y) ≅ B.inclusion.obj X.left) :
    (Space.relativeHom B S hS (yoneda.obj Z) (yoneda.obj X) (yoneda.obj Q)
      (yoneda.map z) (yoneda.map x)
      (isAlgebraicSpace_yoneda B S hS Z)
      (isAlgebraicSpace_yoneda B S hS X)
      (isAlgebraicSpace_yoneda B S hS Q)).IsRepresentable := by
  let : HasBinaryProducts (Over Q) := Over.ConstructProducts.over_binaryProduct_of_pullback
  obtain ⟨W, hsize, ⟨r⟩⟩ := relativeHom_representableBy_coproduct_size_le
    Y (B.inclusion.map z.left) (e.hom ≫ B.inclusion.map x.left)
  rw [Scheme.size_congr e] at hsize
  let W₀ : B.Schemes := B.obj (hsize.trans_lt (max_lt Q.left.property X.left.property))
  let w : W₀ ⟶ Q.left := ObjectProperty.homMk W.hom
  let W₁ : Over Q.left := Over.mk w
  let W₂ : Over Q := (Over.iteratedSliceBackward Q).obj W₁
  let F : Over Q ⥤ Over (B.inclusion.obj Q.left) :=
    (Over.iteratedSliceEquiv Q).functor ⋙ Over.post B.inclusion
  let eX : Over.mk (e.hom ≫ B.inclusion.map x.left) ≅
      Over.mk (B.inclusion.map x.left) := Over.isoMk e rfl
  let r₀ := r.ofIso (Functor.isoWhiskerLeft
    (prod.functor.obj (Over.mk (B.inclusion.map z.left))).op (yoneda.mapIso eX))
  let r' : ((prod.functor.obj (Over.mk z)).op ⋙ yoneda.obj (Over.mk x)).RepresentableBy W₂ :=
    relativeHomRepresentableBy_of_fullyFaithful F (Over.mk z) (Over.mk x) W₂ r₀
  exact (relativeHomRepresentableByOfOver B S hS z x W₂ r').isRepresentable


end AlgebraicGeometry.RelativeHomAffineTarget

namespace AlgebraicGeometry

/-- **A scheme isomorphic to a disjoint union of affine schemes is separated.** The disjoint union
of a family of affine schemes is affine over the disjoint union of their spectra, which is affine,
so the structure morphism to the terminal scheme is separated. -/
theorem isSeparated_of_coproduct_affine {V : Scheme.{u}}
    {I : Type u} (Y : I → Scheme.{u}) [∀ i, IsAffine (Y i)] (e : (∐ Y) ≅ V) :
    V.IsSeparated := by
  let k := e.inv ≫ (Sigma.mapIso (fun i => Scheme.isoSpec (Y i))).hom ≫
    sigmaSpec (fun i => Γ(Y i, ⊤))
  have : IsSeparated k := by dsimp [k]; infer_instance
  constructor
  rw [← terminal.comp_from k]
  infer_instance

namespace Space

/-! ### Transport of the relative morphism functor along an isomorphism of the source -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section SourceIso

variable {Z Z' X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q} {z' : Z' ⟶ Q} {x : X ⟶ Q}

/-- **The comparison map of base changes induced by a morphism of the sources.** For `s : Z' ⟶ Z`
with `s ≫ z = z'`, the base change `T ×_{a, Q} Z'` maps to `T ×_{a, Q} Z`, by `s` on the second
component. -/
noncomputable def relativeMorphismSourceComparison (z : Z ⟶ Q) (z' : Z' ⟶ Q) (s : Z' ⟶ Z)
    (hs : s ≫ z = z')
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : T ⟶ Q) : pullback a z' ⟶ pullback a z :=
  pullback.lift (pullback.fst a z') (pullback.snd a z' ≫ s)
    (by rw [Category.assoc, hs]; exact pullback.condition)

/-- The first component of `relativeMorphismSourceComparison` is the first projection. -/
@[simp, reassoc (attr := simp)]
theorem relativeMorphismSourceComparison_fst (z : Z ⟶ Q) (z' : Z' ⟶ Q) (s : Z' ⟶ Z)
    (hs : s ≫ z = z')
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : T ⟶ Q) :
    relativeMorphismSourceComparison z z' s hs a ≫ pullback.fst a z = pullback.fst a z' :=
  pullback.lift_fst _ _ _

/-- The second component of `relativeMorphismSourceComparison` is the second projection followed
by `s`. -/
@[simp, reassoc (attr := simp)]
theorem relativeMorphismSourceComparison_snd (z : Z ⟶ Q) (z' : Z' ⟶ Q) (s : Z' ⟶ Z)
    (hs : s ≫ z = z')
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : T ⟶ Q) :
    relativeMorphismSourceComparison z z' s hs a ≫ pullback.snd a z = pullback.snd a z' ≫ s :=
  pullback.lift_snd _ _ _

/-- **The comparison map of base changes induced by a morphism of the test objects**, for a base
that factors through it only up to a given equality. -/
noncomputable def relativeMorphismBaseComparison (z' : Z' ⟶ Q)
    {T U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : U ⟶ Q} {b : T ⟶ Q} (t : U ⟶ T) (hab : a = t ≫ b) : pullback a z' ⟶ pullback b z' :=
  pullback.lift (pullback.fst a z' ≫ t) (pullback.snd a z')
    (by rw [Category.assoc, ← hab]; exact pullback.condition)

/-- The first component of `relativeMorphismBaseComparison` is the first projection followed by
`t`. -/
@[simp, reassoc (attr := simp)]
theorem relativeMorphismBaseComparison_fst (z' : Z' ⟶ Q) {T U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : U ⟶ Q} {b : T ⟶ Q} (t : U ⟶ T) (hab : a = t ≫ b) :
    relativeMorphismBaseComparison z' t hab ≫ pullback.fst b z' = pullback.fst a z' ≫ t :=
  pullback.lift_fst _ _ _

/-- The second component of `relativeMorphismBaseComparison` is the second projection. -/
@[simp, reassoc (attr := simp)]
theorem relativeMorphismBaseComparison_snd (z' : Z' ⟶ Q) {T U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : U ⟶ Q} {b : T ⟶ Q} (t : U ⟶ T) (hab : a = t ≫ b) :
    relativeMorphismBaseComparison z' t hab ≫ pullback.snd b z' = pullback.snd a z' :=
  pullback.lift_snd _ _ _

/-- **Precomposition of a pair of Stacks 05Y1 with a morphism of the sources.** A morphism
`s : Z' ⟶ Z` over `Q` turns a pair for `z : Z ⟶ Q` into a pair for `z' : Z' ⟶ Q`, by base
changing the second component along `s`. -/
noncomputable def RelativeMorphism.precomp (s : Z' ⟶ Z) (hs : s ≫ z = z')
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : RelativeMorphism B S hS Z X Q z x T) :
    RelativeMorphism B S hS Z' X Q z' x T where
  base := p.base
  morphism := relativeMorphismSourceComparison z z' s hs p.base ≫ p.morphism
  commutes := by
    rw [Category.assoc, p.commutes, ← Category.assoc, relativeMorphismSourceComparison_snd,
      Category.assoc, hs]

/-- Precomposition with a morphism of the sources does not change the base of a pair. -/
@[simp] theorem RelativeMorphism.precomp_base (s : Z' ⟶ Z) (hs : s ≫ z = z')
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : RelativeMorphism B S hS Z X Q z x T) :
    (RelativeMorphism.precomp s hs p).base = p.base := rfl

/-- The morphism of `RelativeMorphism.precomp s hs p` is that of `p` precomposed with
`relativeMorphismSourceComparison`. -/
@[simp] theorem RelativeMorphism.precomp_morphism (s : Z' ⟶ Z) (hs : s ≫ z = z')
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : RelativeMorphism B S hS Z X Q z x T) :
    (RelativeMorphism.precomp s hs p).morphism =
      relativeMorphismSourceComparison z z' s hs p.base ≫ p.morphism := rfl

/-- **An isomorphism of the sources over `Q` identifies the pairs of Stacks 05Y1.** -/
noncomputable def relativeMorphismSourceIsoEquiv (e : Z ≅ Z') (he : e.hom ≫ z' = z)
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    RelativeMorphism B S hS Z X Q z x T ≃ RelativeMorphism B S hS Z' X Q z' x T where
  toFun := RelativeMorphism.precomp (z := z) (z' := z') e.inv
    (by rw [← he, Iso.inv_hom_id_assoc])
  invFun := RelativeMorphism.precomp (z := z') (z' := z) e.hom he
  left_inv p := by
    refine RelativeMorphism.ext_of_base_eq rfl ?_
    dsimp only [RelativeMorphism.precomp]
    rw [← Category.assoc]
    congr 1
    refine pullback.hom_ext ?_ ?_ <;> simp [pullback.congrHom]
  right_inv p := by
    refine RelativeMorphism.ext_of_base_eq rfl ?_
    dsimp only [RelativeMorphism.precomp]
    rw [← Category.assoc]
    congr 1
    refine pullback.hom_ext ?_ ?_ <;> simp [pullback.congrHom]

/-- **A realization of the relative morphism functor transported along an isomorphism of the
source.** The functor and its projection are unchanged — an isomorphism of the sources over `Q`
does not change the pairs of Stacks 05Y1, only their presentation — and the identification of the
sections with pairs is composed with
`AlgebraicGeometry.Space.relativeMorphismSourceIsoEquiv`. -/
noncomputable def RelativeHomConstruction.ofSourceIso
    (H : RelativeHomConstruction B S hS Z X Q z x) (e : Z ≅ Z') (he : e.hom ≫ z' = z) :
    RelativeHomConstruction B S hS Z' X Q z' x where
  functor := H.functor
  projection := H.projection
  sections T := (H.sections T).trans (relativeMorphismSourceIsoEquiv e he (yoneda.obj T))
  projection_sections T p := H.projection_sections T p
  sections_map {T U} f p := by
    obtain ⟨hbase, h, hfst, hsnd, hm⟩ := H.sections_map f p
    dsimp only [relativeMorphismSourceIsoEquiv, Equiv.trans_apply, Equiv.coe_fn_mk,
      RelativeMorphism.precomp_base, RelativeMorphism.precomp_morphism]
    refine ⟨hbase, relativeMorphismBaseComparison z' (yoneda.map f) hbase,
      relativeMorphismBaseComparison_fst .., relativeMorphismBaseComparison_snd .., ?_⟩
    rw [hm]
    simp only [← Category.assoc]
    congr 1
    refine pullback.hom_ext ?_ ?_
    · simp [hfst]
    · simp [hsnd]
end SourceIso

/-- **The case of Stacks 05Y7 in which everything is an object of the site.** Let `z : Z ⟶ Q` and
`x : X ⟶ Q` be morphisms of objects of the big fppf site over `S`, let the scheme underlying `z`
be finite locally free, let the scheme underlying `Q` be separated, and let the scheme underlying
`X` be a disjoint union of affine schemes. Then the relative morphism functor `Mor_Q(Z, X)` of
Stacks 05Y2 is an algebraic space over `S` — indeed it is represented by an object of the site.

The separatedness hypothesis and the shape of the target are what the covering of Stacks 03FX
produces, and `AlgebraicGeometry.isSeparated_of_coproduct_affine` discharges the first from the
second. -/
theorem isAlgebraicSpace_relativeHom_of_coproductAffine
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (Z X Q : BigFppfOver B S hS) (z : Z ⟶ Q) (x : X ⟶ Q)
    (hz : Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map z))
    (hQ : ((BigFppfOver.toScheme B S hS).obj Q).IsSeparated)
    {I : Type u} (Y : I → Scheme.{u}) (hY : ∀ i, IsAffine (Y i))
    (e : (∐ Y) ≅ (BigFppfOver.toScheme B S hS).obj X) :
    IsAlgebraicSpace B S hS
      (relativeHom B S hS (yoneda.obj Z) (yoneda.obj X) (yoneda.obj Q)
        (yoneda.map z) (yoneda.map x)
        (isAlgebraicSpace_yoneda B S hS Z)
        (isAlgebraicSpace_yoneda B S hS X)
        (isAlgebraicSpace_yoneda B S hS Q)) := by
  let : Stacks.Morphisms.IsFiniteLocallyFree (B.inclusion.map z.left) := hz
  let : ((B.inclusion.obj Q.left)).IsSeparated := hQ
  let : ∀ i, IsAffine (Y i) := hY
  let : (relativeHom B S hS (yoneda.obj Z) (yoneda.obj X) (yoneda.obj Q)
      (yoneda.map z) (yoneda.map x)
      (isAlgebraicSpace_yoneda B S hS Z)
      (isAlgebraicSpace_yoneda B S hS X)
      (isAlgebraicSpace_yoneda B S hS Q)).IsRepresentable :=
    RelativeHomAffineTarget.isRepresentable_relativeHom_coproduct B S hS Z X Q z x Y e
  exact isAlgebraicSpace_of_isRepresentable B S hS _

/-! ### Stacks 05Y7 by base change to a representable base -/

/-- **Stacks 05Y7, with the input from Stacks 05XR carried.** Let `S` be a scheme contained in a
big fppf site, and let `z : Z ⟶ Q` and `x : X ⟶ Q` be morphisms of algebraic spaces over `S` with
`z` finite locally free. Then the relative morphism functor `Mor_Q(Z, X)` of Stacks 05Y2 is an
algebraic space over `S`.

Nothing is assumed about `X`; in particular this discharges the hypothesis `hrepresentable` of
`AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_of_isFiniteLocallyFree`. The hypothesis
`h05XR` is Stacks 05XR in the form the proofs of Stacks 05Y5 use it, which is **no longer an open
assumption** — it is the theorem `AlgebraicGeometry.Space.isFibreSectionsAlgebraicEtale` — and is
carried only because that theorem is proved downstream of this file.

The proof is the source's base change. A surjective étale chart `h_V ⟶ Q` with `V` an object of
the site whose underlying scheme is a disjoint union of affine schemes (Stacks 03FX) makes the
base `V` separated; Stacks 05Y4 identifies `Mor_V(Z_V, X_V)` with the base change of
`Mor_Q(Z, X)` along it, so Stacks 03Y3 reduces the claim to the base `h_V`. There `Z_V` is
represented by an object of the site, because a finite locally free morphism is affine and hence
relatively representable (Stacks 03WG and Stacks 03ZU), and finite local freeness survives the
base change; and the target is reduced to a disjoint union of affine schemes by Stacks 03FX again
and the reduction on the target of Stacks 05Y5, leaving
`AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_of_coproductAffine`. -/
theorem isAlgebraicSpace_relativeHom_of_isFiniteLocallyFree_of_fibreSections
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (z : Z ⟶ Q) (x : X ⟶ Q)
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q)
    (hz : IsFiniteLocallyFree B S hS
      (ObjectProperty.homMk z :
        (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ (⟨Q, hQ⟩ : AlgebraicSpaces B S hS)))
    (h05XR : ∀ (X'' X' Z' Q' : AlgebraicSpaces B S hS) (g : X'' ⟶ X') (z' : Z' ⟶ Q'),
      IsFibreSectionsAlgebraicEtale B S hS g z') :
    IsAlgebraicSpace B S hS (relativeHom B S hS Z X Q z x hZ hX hQ) := by
  obtain ⟨V, ξ, I, Y, eV, hξsurj, hξetale, hYaff, -⟩ :=
    exists_etale_surjective_coproduct_affine_cover B S hS Q hQ
  have hξetale' : IsEtale B S hS ξ := isEtale_of_presheaf_etale B S hS hξetale
  have hξsurj' : IsSurjective B S hS ξ := isSurjective_of_presheafSurjective B S hS ξ hξsurj
  have hVsep : ((BigFppfOver.toScheme B S hS).obj V).IsSeparated := by
    let : ∀ i, IsAffine (Y i) := hYaff
    exact isSeparated_of_coproduct_affine Y eV
  have hQ' : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  have hX' : IsAlgebraicSpace B S hS (pullback ξ x) :=
    isAlgebraicSpace_pullback B S hS ξ x hQ' hX hQ
  -- the base change of `z` is represented by an object of the site, finite locally free over `V`
  have hrep : yoneda.relativelyRepresentable
      (ObjectProperty.homMk z :
        (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ (⟨Q, hQ⟩ : AlgebraicSpaces B S hS)).hom :=
    relativelyRepresentable_of_isAffineHom B S hS _ hz.1
  have hpres := presheaf_of_isFiniteLocallyFree B S hS
    (ObjectProperty.homMk z :
      (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ (⟨Q, hQ⟩ : AlgebraicSpaces B S hS)) hrep hz
  set W : BigFppfOver B S hS := hpres.rep.pullback ξ with hWdef
  set p : W ⟶ V := hpres.rep.snd ξ with hpdef
  have sq : IsPullback (hpres.rep.fst ξ) (yoneda.map p) z ξ := hpres.rep.isPullback ξ
  have hpflf : Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map p) :=
    isFiniteLocallyFree_of_isPullback_of_isFiniteLocallyFree B S hS _ hrep hz ξ
      (hpres.rep.fst ξ) p sq
  have hW : IsAlgebraicSpace B S hS (yoneda.obj W) := isAlgebraicSpace_yoneda B S hS W
  -- finite local freeness of the base change, in the sense of Stacks 03ZV
  have sqSpace : IsPullback
      (ObjectProperty.homMk (hpres.rep.fst ξ) :
        (⟨yoneda.obj W, hW⟩ : AlgebraicSpaces B S hS) ⟶ (⟨Z, hZ⟩ : AlgebraicSpaces B S hS))
      (ObjectProperty.homMk (yoneda.map p) :
        (⟨yoneda.obj W, hW⟩ : AlgebraicSpaces B S hS) ⟶
          (⟨yoneda.obj V, hQ'⟩ : AlgebraicSpaces B S hS))
      (ObjectProperty.homMk z :
        (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ (⟨Q, hQ⟩ : AlgebraicSpaces B S hS))
      (ObjectProperty.homMk ξ :
        (⟨yoneda.obj V, hQ'⟩ : AlgebraicSpaces B S hS) ⟶
          (⟨Q, hQ⟩ : AlgebraicSpaces B S hS)) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι (IsAlgebraicSpace B S hS)) sq
  have hzW : IsFiniteLocallyFree B S hS
      (ObjectProperty.homMk (yoneda.map p) :
        (⟨yoneda.obj W, hW⟩ : AlgebraicSpaces B S hS) ⟶
          (⟨yoneda.obj V, hQ'⟩ : AlgebraicSpaces B S hS)) :=
    ((isFiniteLocallyFree_iff_isAffineHom_and_baseChange B S hS _ _ _ _ sqSpace
      hξetale' hξsurj').mp hz).2
  -- the reduction on the target over the representable base `h_V`
  obtain ⟨U, c, J, Yt, eU, hcsurj, hcetale, hYtaff, -⟩ :=
    exists_etale_surjective_coproduct_affine_cover B S hS (pullback ξ x) hX'
  have hU : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  set u : U ⟶ V := yoneda.preimage (c ≫ pullback.fst ξ x) with hudef
  have hu : yoneda.map u = c ≫ pullback.fst ξ x := yoneda.map_preimage _
  have hchart : IsAlgebraicSpace B S hS
      (relativeHom B S hS (yoneda.obj W) (yoneda.obj U) (yoneda.obj V)
        (yoneda.map p) (yoneda.map u) hW hU hQ') :=
    isAlgebraicSpace_relativeHom_of_coproductAffine B S hS W U V p u hpflf hVsep Yt hYtaff eU
  have hbc : IsAlgebraicSpace B S hS
      (relativeHomData B S hS (yoneda.obj W) (pullback ξ x) (yoneda.obj V)
        (yoneda.map p) (pullback.fst ξ x) hW hX' hQ').functor :=
    isAlgebraicSpace_relativeHom_of_etaleSurjectiveTarget
      (X' := (⟨yoneda.obj U, hU⟩ : AlgebraicSpaces B S hS))
      (X := (⟨pullback ξ x, hX'⟩ : AlgebraicSpaces B S hS))
      (Z := (⟨yoneda.obj W, hW⟩ : AlgebraicSpaces B S hS))
      (Q := (⟨yoneda.obj V, hQ'⟩ : AlgebraicSpaces B S hS))
      (x' := ObjectProperty.homMk (yoneda.map u)) (x := ObjectProperty.homMk (pullback.fst ξ x))
      (z := ObjectProperty.homMk (yoneda.map p))
      (relativeHomData B S hS (yoneda.obj W) (yoneda.obj U) (yoneda.obj V)
        (yoneda.map p) (yoneda.map u) hW hU hQ')
      (relativeHomData B S hS (yoneda.obj W) (pullback ξ x) (yoneda.obj V)
        (yoneda.map p) (pullback.fst ξ x) hW hX' hQ')
      (ObjectProperty.homMk c) hu.symm
      (isEtale_of_presheaf_etale B S hS hcetale)
      (isSurjective_of_presheafSurjective B S hS c hcsurj) hzW
      (h05XR (⟨yoneda.obj U, hU⟩ : AlgebraicSpaces B S hS)
        (⟨pullback ξ x, hX'⟩ : AlgebraicSpaces B S hS)
        (⟨yoneda.obj W, hW⟩ : AlgebraicSpaces B S hS)
        (⟨yoneda.obj V, hQ'⟩ : AlgebraicSpaces B S hS)
        (ObjectProperty.homMk c) (ObjectProperty.homMk (yoneda.map p)))
      (isSheaf_relativeHom B S hS (yoneda.obj W) (pullback ξ x) (yoneda.obj V)
        (yoneda.map p) (pullback.fst ξ x) hW hX' hQ') hchart
  -- transport the source along the identification of `Z_V` with `h_W`, and descend
  set H := relativeHomData B S hS Z X Q z x hZ hX hQ with hHdef
  set H' := (relativeHomData B S hS (yoneda.obj W) (pullback ξ x) (yoneda.obj V)
    (yoneda.map p) (pullback.fst ξ x) hW hX' hQ').ofSourceIso sq.flip.isoPullback
    sq.flip.isoPullback_hom_fst with hH'def
  have hbcs : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hbce : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hsq := isPullback_relativeHomOfBaseChange ξ H H'
  have hfrep : IsRepresentableByAlgebraicSpaces B S hS (relativeHomOfBaseChange ξ H H') :=
    isRepresentableByAlgebraicSpaces_of_isPullback B S hS H'.projection
      (relativeHomOfBaseChange ξ H H') ξ H.projection hsq
      (isRepresentableByAlgebraicSpaces_of_isAlgebraicSpace B S hS hQ' hQ ξ)
  have hfsurj : (MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (relativeHomOfBaseChange ξ H H') :=
    MorphismProperty.of_isPullback hsq hξsurj
  have hfetale : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (relativeHomOfBaseChange ξ H H') :=
    MorphismProperty.of_isPullback hsq hξetale
  exact isAlgebraicSpace_of_isRepresentableByAlgebraicSpaces_surjective_etale
    (isSheaf_relativeHom B S hS Z X Q z x hZ hX hQ) hbc (relativeHomOfBaseChange ξ H H') hfrep
    (hasProperty_surjectiveMorphismProperty_of_isSurjective _ _ _ _ hfrep
      (isSurjective_of_presheafSurjective B S hS _ hfsurj))
    fun T ζ => isEtale_of_presheaf_etale B S hS
      (MorphismProperty.pullback_fst ζ (relativeHomOfBaseChange ξ H H') hfetale)

end Space

end AlgebraicGeometry

end
