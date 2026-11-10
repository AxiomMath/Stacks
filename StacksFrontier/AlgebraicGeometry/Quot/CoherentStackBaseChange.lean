module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackFibered
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackProjection
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.CategoryTheory.TwoFibreProduct.BasedCategoryLifting
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver

/-!
# Infrastructure for base change of the stack of coherent sheaves (Stacks 08LP)

Let `f : X ⟶ Y` be a finitely presented morphism of algebraic spaces over a scheme `S` of a big
fppf site, the standing data of Stacks 08KB, and let `g : Y' ⟶ Y` be a morphism of algebraic
spaces.  Writing `X' = X ×_Y Y'`, the projection `f' : X' ⟶ Y'` is again finitely presented, so
it is again a standing datum, and Stacks 08LP asserts that the square

`Coh_{X'/Y'} ⟶ Coh_{X/Y}`, `𝒮_{Y'} ⟶ 𝒮_Y`

is 2-cartesian.

This file carries everything that square is built from which does not mention the base-change
stability of the conditions defining an object of `Coh_{X/Y}`: the base-changed standing datum,
the comparison `X'_T ≅ X_T` of the two base changes at a test scheme `T` over `Y'` with its
naturality and the comparison of the two iterated inverse images along it, the conjugation
calculus for the module comparison a morphism of `Coh_{X/Y}` carries, and the coherences of
Stacks 03LU those need.

**The square itself, its universal property and Stacks 08LP are not here.**  They are built on
this in `StacksFrontier/AlgebraicGeometry/Quot/CoherentStackBaseChangeUnconditional.lean`, which
needs only the finite-presentation form of the base-change stability — a theorem rather than an
assumption — and so proves them with nothing assumed.  This file once carried a second copy of
that whole chain, from the transport of an object to the 2-cartesian square, resting on the
stronger `AlgebraicGeometry.Space.ModulePullbackStability`, which has no value in this
development; those twenty-six declarations had no consumer left once the unconditional chain
existed, and they have been removed.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.baseChange`: the base-changed standing datum
  `f' : X ×_Y Y' ⟶ Y'`.
* `AlgebraicGeometry.Space.CoherentSituation.overBase`: reading a test scheme over `Y'` as one
  over `Y`.
* `AlgebraicGeometry.Space.CoherentSituation.baseChangeSpaceIso`: the comparison `X'_T ≅ X_T` of
  the two base changes at a test scheme `T` over `Y'`.
* `CategoryTheory.Functor.conjFibre`: the conjugate of a fibre morphism by a comparison of
  iterated functors over a square, which is the shape of base change of the module comparison
  carried by a morphism of `Coh_{X/Y}`.
* `AlgebraicGeometry.Space.CoherentSituation.baseChangeModuleSquare`: that comparison for the
  square of a morphism of test schemes.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.baseChangeSpaceIso_naturality` and
  `AlgebraicGeometry.Space.CoherentSituation.baseChangeSpaceIso_inv_naturality`: the comparison
  of base changes is natural in the test scheme.
* `AlgebraicGeometry.Space.CoherentSituation.isPullback_baseChangeSpaceIso_inv`: the comparison
  sits in a cartesian square over the identity of the test scheme, which is what lets the
  base-change stability of the conditions defining an object of `Coh_{X/Y}` be applied to it.
* `CategoryTheory.Functor.conjFibre_id` and `CategoryTheory.Functor.conjFibre_fibreComp`: the
  unit and composition laws for conjugation of fibre morphisms, each taking the relevant
  coherence of the comparisons as a hypothesis in the shape a consumer already has it.
* `AlgebraicGeometry.Space.modulePullbackSquare_id` and
  `AlgebraicGeometry.Space.modulePullbackSquare_comp`: those two coherences for the comparisons
  of inverse images of Stacks 03LU — the comparison for a square whose two horizontal sides are
  identities, and the pasting of two squares side by side.  Together with the two laws above
  they are exactly the input the functoriality of base change needs, which the unconditional
  module consumes.
* `AlgebraicGeometry.Space.modulePullbackTriangle_id_left`,
  `AlgebraicGeometry.Space.modulePullbackTriangle_id_right` and
  `AlgebraicGeometry.Space.modulePullbackTriangle_comp_id`: the unit laws of Stacks 03LU for
  arbitrary morphisms of algebraic spaces, which is the generality those two coherences need.
* `AlgebraicGeometry.Space.coherentHom_eq_of_heq`: two morphisms of `Coh_{X/Y}` with the same
  base map and the same comparison of modules are equal, the comparison being compared
  heterogeneously.
* `AlgebraicGeometry.Space.CoherentSituation.baseChangeModuleSquare_id` and
  `AlgebraicGeometry.Space.CoherentSituation.baseChangeModuleSquare_comp_eq`: the unit and
  composition laws of that comparison, in the shape the functoriality of the transport needs.
* `AlgebraicGeometry.Space.CoherentSituation.fullyFaithful_modulePullback_baseChangeSpaceIso`:
  the inverse image along the comparison of base changes is fully faithful, which is what makes
  the transport of a morphism lose nothing.

## Implementation notes

The base change `X'_T` of `X'` to a test scheme `T` over `Y'` is the iterated fibre product
`(X ×_Y Y') ×_{Y'} T`, and the base change `X_T` of `X` to the same test scheme read over `Y` is
`X ×_Y T`.  The comparison between them is the pasting isomorphism
`CategoryTheory.Limits.pullbackLeftPullbackSndIso` of presheaves, which is why it is an
isomorphism on the nose rather than only up to a further choice.

Reading a test scheme over `Y'` as a test scheme over `Y` is
`CategoryTheory.CostructuredArrow.map` at `g`; it does not change the underlying scheme, which is
why the square of Stacks 08LP commutes over the big fppf site on the nose.

That the transported module is again quasi-coherent, of finite presentation, flat over the test
scheme and of proper support is a base-change stability, and it is the reason the transport
itself is not in this file: see the unconditional module, which takes the form of that stability
which is a theorem.  What this file supplies towards it is
`AlgebraicGeometry.Space.CoherentSituation.isPullback_baseChangeSpaceIso_inv`, the cartesian
square over the identity of the test scheme to which any such stability is applied.

**Every coherence of the comparisons of inverse images is stated at the level of isomorphisms of
functors, never of their components.**  The comparisons contain `CategoryTheory.eqToIso` factors,
and the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardCoherence.lean` record that the
kernel does not finish checking a proof of a statement that projects the underlying morphism of
such an isomorphism.  The conjugation calculus
`CategoryTheory.Functor.conjFibre` is where the two levels meet: it is stated for an abstract
comparison, so that a consumer is left with a syntactic match at the point of use.  For the same
reason the functoriality of base change compares two morphisms of `Coh_{X/Y}` through
`AlgebraicGeometry.Space.coherentHom_eq_of_heq`, supplied here, rather than through
`AlgebraicGeometry.Space.CoherentHom.ext`, and each identification of two spellings of one test
object is a separate declaration: the kernel budget is per declaration, and these
identifications are cheap one at a time and not in bulk.

`𝒮_Y` is the category of test schemes of the site over `Y`,
`AlgebraicGeometry.Space.baseBasedCategory`; by the Yoneda lemma a morphism `T ⟶ Y` of algebraic
spaces with `T` a scheme of the site is an element of `Y` over `T`, so this is the category of
elements of the functor of points of `Y`, that is the category fibred in sets attached to `Y`.
That is the vocabulary in which the square is stated; the square is formed in the strict
2-category of categories over the site, in the unconditional module.

## References

* [Stacks Project, Tag 08LP](https://stacks.math.columbia.edu/tag/08LP)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 08W5](https://stacks.math.columbia.edu/tag/08W5)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03XR](https://stacks.math.columbia.edu/tag/03XR)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- The companion of `CategoryTheory.Functor.trans_isoWhiskerLeft_trans` for whiskering on the
right. -/
theorem trans_isoWhiskerRight_trans' {C : Type*} {D : Type*} {E : Type*} [Category* C]
    [Category* D] [Category* E] {G H K : C ⥤ D} (F : D ⥤ E) {X : C ⥤ E} (ξ : X ≅ G ⋙ F)
    (α : G ≅ H) (β : H ≅ K) :
    (ξ ≪≫ isoWhiskerRight α F) ≪≫ isoWhiskerRight β F = ξ ≪≫ isoWhiskerRight (α ≪≫ β) F := by
  rw [isoWhiskerRight_trans, Iso.trans_assoc]

/-- The conjugate of a fibre morphism by a comparison of iterated functors over a square.

Let `Lp : 𝒜₁ ⥤ 𝒜₀` and `Lq : ℬ₁ ⥤ ℬ₀` be two "horizontal" functors, let `E₀ : 𝒜₀ ⥤ ℬ₀` and
`E₁ : 𝒜₁ ⥤ ℬ₁` be two "vertical" ones, and let `σ : E₁ ⋙ Lq ≅ Lp ⋙ E₀` compare the two ways
round the square.  A fibre morphism `φ : Lp.obj M' ⟶ M` then has a conjugate
`Lq.obj (E₁.obj M') ⟶ E₀.obj M`: apply `E₀` to it and read its source through `σ`.

This is the shape of "base change of a fibre morphism": `Lp` and `Lq` are the inverse images
along the two induced morphisms of base changes and `E₀`, `E₁` the inverse images along the
comparison of the two base changes. -/
def conjFibre {𝒜₀ : Type*} {𝒜₁ : Type*} {ℬ₀ : Type*} {ℬ₁ : Type*} [Category* 𝒜₀] [Category* 𝒜₁]
    [Category* ℬ₀] [Category* ℬ₁] {Lp : 𝒜₁ ⥤ 𝒜₀} {E₀ : 𝒜₀ ⥤ ℬ₀} {E₁ : 𝒜₁ ⥤ ℬ₁} {Lq : ℬ₁ ⥤ ℬ₀}
    (σ : E₁ ⋙ Lq ≅ Lp ⋙ E₀) {M : 𝒜₀} {M' : 𝒜₁} (φ : Lp.obj M' ⟶ M) :
    Lq.obj (E₁.obj M') ⟶ E₀.obj M :=
  σ.hom.app M' ≫ E₀.map φ

/-- The conjugate of an isomorphism of fibres is an isomorphism. -/
instance isIso_conjFibre {𝒜₀ : Type*} {𝒜₁ : Type*} {ℬ₀ : Type*} {ℬ₁ : Type*} [Category* 𝒜₀]
    [Category* 𝒜₁] [Category* ℬ₀] [Category* ℬ₁] {Lp : 𝒜₁ ⥤ 𝒜₀} {E₀ : 𝒜₀ ⥤ ℬ₀} {E₁ : 𝒜₁ ⥤ ℬ₁}
    {Lq : ℬ₁ ⥤ ℬ₀} (σ : E₁ ⋙ Lq ≅ Lp ⋙ E₀) {M : 𝒜₀} {M' : 𝒜₁} (φ : Lp.obj M' ⟶ M) [IsIso φ] :
    IsIso (conjFibre σ φ) := by
  change IsIso (σ.hom.app M' ≫ E₀.map φ)
  infer_instance

/-- **The unit law for conjugation of fibre morphisms.**  If the comparison `σ` identifies the
two ways round the square with the two identifications `γ'`, `γ` of the horizontal functors with
the identity, then conjugating the component of `γ'` gives the component of `γ`. -/
theorem conjFibre_id {𝒜 : Type*} {ℬ : Type*} [Category* 𝒜] [Category* ℬ] {Lp : 𝒜 ⥤ 𝒜}
    {Lq : ℬ ⥤ ℬ} {E : 𝒜 ⥤ ℬ} (σ : E ⋙ Lq ≅ Lp ⋙ E) (γ' : Lp ≅ 𝟭 𝒜) (γ : Lq ≅ 𝟭 ℬ)
    (hfac : σ ≪≫ isoWhiskerRight γ' E ≪≫ leftUnitor E =
      isoWhiskerLeft E γ ≪≫ rightUnitor E) (M : 𝒜) :
    conjFibre σ (γ'.hom.app M) = γ.hom.app (E.obj M) := by
  have h := NatTrans.congr_app (congrArg Iso.hom hfac) M
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, whiskerRight_app,
    isoWhiskerLeft_hom, whiskerLeft_app, leftUnitor_hom_app, rightUnitor_hom_app] at h
  simpa [conjFibre] using h

/-- **The composition law for conjugation of fibre morphisms.**  If the comparison `σ` for a
composite factors through the comparisons `σ₁`, `σ₂` for the two factors and the comparisons
`τ`, `υ` of the two horizontal composites, then conjugating a composite of fibre morphisms is
the composite of their conjugates. -/
theorem conjFibre_fibreComp {𝒜₀ : Type*} {𝒜₁ : Type*} {𝒜₂ : Type*} {ℬ₀ : Type*} {ℬ₁ : Type*}
    {ℬ₂ : Type*} [Category* 𝒜₀] [Category* 𝒜₁] [Category* 𝒜₂] [Category* ℬ₀] [Category* ℬ₁]
    [Category* ℬ₂] {Lp₁ : 𝒜₁ ⥤ 𝒜₀} {Lp₂ : 𝒜₂ ⥤ 𝒜₁} {Lp : 𝒜₂ ⥤ 𝒜₀} (τ : Lp ≅ Lp₂ ⋙ Lp₁)
    {Lq₁ : ℬ₁ ⥤ ℬ₀} {Lq₂ : ℬ₂ ⥤ ℬ₁} {Lq : ℬ₂ ⥤ ℬ₀} (υ : Lq ≅ Lq₂ ⋙ Lq₁)
    {E₀ : 𝒜₀ ⥤ ℬ₀} {E₁ : 𝒜₁ ⥤ ℬ₁} {E₂ : 𝒜₂ ⥤ ℬ₂} (σ₁ : E₁ ⋙ Lq₁ ≅ Lp₁ ⋙ E₀)
    (σ₂ : E₂ ⋙ Lq₂ ≅ Lp₂ ⋙ E₁) (σ : E₂ ⋙ Lq ≅ Lp ⋙ E₀)
    (hfac : σ ≪≫ isoWhiskerRight τ E₀ =
      isoWhiskerLeft E₂ υ ≪≫ isoWhiskerRight σ₂ Lq₁ ≪≫ isoWhiskerLeft Lp₂ σ₁)
    {M : 𝒜₀} {M' : 𝒜₁} {M'' : 𝒜₂} (a : Lp₁.obj M' ⟶ M) (b : Lp₂.obj M'' ⟶ M') :
    conjFibre σ (fibreComp τ a b) = fibreComp υ (conjFibre σ₁ a) (conjFibre σ₂ b) := by
  have h := NatTrans.congr_app (congrArg Iso.hom hfac) M''
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, whiskerRight_app,
    isoWhiskerLeft_hom, whiskerLeft_app] at h
  have hn := σ₁.hom.naturality b
  dsimp at hn
  simp only [conjFibre, fibreComp, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, reassoc_of% h]

/-- A morphism of a category fibred in groupoids lying over an identity is an isomorphism. -/
theorem isIso_of_isHomLift_id' {𝒮 : Type*} {𝒞 : Type*} [Category* 𝒮] [Category* 𝒞] (p : 𝒮 ⥤ 𝒞)
    (hp : p.IsFiberedInGroupoids) {U : 𝒞} {a b : 𝒮} (φ : a ⟶ b)
    (hφ : p.IsHomLift (𝟙 U) φ) : IsIso φ := by
  have : p.IsStronglyCartesian (𝟙 U) φ :=
    Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift hp (𝟙 U) φ
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso p (𝟙 U) φ

/-- The fibre morphism whose conjugate is a given one. -/
def conjFibreInv {𝒜₀ : Type*} {𝒜₁ : Type*} {ℬ₀ : Type*} {ℬ₁ : Type*} [Category* 𝒜₀]
    [Category* 𝒜₁] [Category* ℬ₀] [Category* ℬ₁] {Lp : 𝒜₁ ⥤ 𝒜₀} {E₀ : 𝒜₀ ⥤ ℬ₀} {E₁ : 𝒜₁ ⥤ ℬ₁}
    {Lq : ℬ₁ ⥤ ℬ₀} (σ : E₁ ⋙ Lq ≅ Lp ⋙ E₀) (hE : E₀.FullyFaithful) {M : 𝒜₀} {M' : 𝒜₁}
    (ψ : Lq.obj (E₁.obj M') ⟶ E₀.obj M) : Lp.obj M' ⟶ M :=
  hE.preimage (σ.inv.app M' ≫ ψ)

/-- The conjugate of `conjFibreInv σ hE ψ` is `ψ`. -/
theorem conjFibre_conjFibreInv {𝒜₀ : Type*} {𝒜₁ : Type*} {ℬ₀ : Type*} {ℬ₁ : Type*} [Category* 𝒜₀]
    [Category* 𝒜₁] [Category* ℬ₀] [Category* ℬ₁] {Lp : 𝒜₁ ⥤ 𝒜₀} {E₀ : 𝒜₀ ⥤ ℬ₀} {E₁ : 𝒜₁ ⥤ ℬ₁}
    {Lq : ℬ₁ ⥤ ℬ₀} (σ : E₁ ⋙ Lq ≅ Lp ⋙ E₀) (hE : E₀.FullyFaithful) {M : 𝒜₀} {M' : 𝒜₁}
    (ψ : Lq.obj (E₁.obj M') ⟶ E₀.obj M) : conjFibre σ (conjFibreInv σ hE ψ) = ψ := by
  simp [conjFibre, conjFibreInv, hE.map_preimage]

/-- If `ψ` is an isomorphism, then so is the fibre morphism `conjFibreInv σ hE ψ`. -/
theorem isIso_conjFibreInv {𝒜₀ : Type*} {𝒜₁ : Type*} {ℬ₀ : Type*} {ℬ₁ : Type*} [Category* 𝒜₀]
    [Category* 𝒜₁] [Category* ℬ₀] [Category* ℬ₁] {Lp : 𝒜₁ ⥤ 𝒜₀} {E₀ : 𝒜₀ ⥤ ℬ₀} {E₁ : 𝒜₁ ⥤ ℬ₁}
    {Lq : ℬ₁ ⥤ ℬ₀} (σ : E₁ ⋙ Lq ≅ Lp ⋙ E₀) (hE : E₀.FullyFaithful) {M : 𝒜₀} {M' : 𝒜₁}
    (ψ : Lq.obj (E₁.obj M') ⟶ E₀.obj M) (hψ : IsIso ψ) : IsIso (conjFibreInv σ hE ψ) := by
  have h : E₀.map (conjFibreInv σ hE ψ) = σ.inv.app M' ≫ ψ := hE.map_preimage _
  have : IsIso (E₀.map (conjFibreInv σ hE ψ)) := by
    rw [h]
    infer_instance
  exact hE.isIso_of_isIso_map _

/-- **A transport lies over an identity.**  A functor sends the transport along an equality of
objects to the transport along the induced equality of images, which lies over the identity of
their common image. -/
theorem isHomLift_id_eqToHom_of_obj_eq {𝒮 : Type*} {𝒳 : Type*} [Category* 𝒮] [Category* 𝒳]
    (p : 𝒳 ⥤ 𝒮)
    {a b : 𝒳} (e : a = b) {U : 𝒮} (h : p.obj a = U) : p.IsHomLift (𝟙 U) (eqToHom e) := by
  subst e
  exact IsHomLift.id h

/-- **Conjugation of fibre morphisms is injective**, the comparison being an isomorphism and the
functor conjugated by fully faithful. -/
theorem conjFibre_injective {𝒜₀ : Type*} {𝒜₁ : Type*} {ℬ₀ : Type*} {ℬ₁ : Type*} [Category* 𝒜₀]
    [Category* 𝒜₁] [Category* ℬ₀] [Category* ℬ₁] {Lp : 𝒜₁ ⥤ 𝒜₀} {E₀ : 𝒜₀ ⥤ ℬ₀} {E₁ : 𝒜₁ ⥤ ℬ₁}
    {Lq : ℬ₁ ⥤ ℬ₀} (σ : E₁ ⋙ Lq ≅ Lp ⋙ E₀) (hE : E₀.FullyFaithful) {M : 𝒜₀} {M' : 𝒜₁}
    {φ ψ : Lp.obj M' ⟶ M} (h : conjFibre σ φ = conjFibre σ ψ) : φ = ψ :=
  hE.map_injective ((cancel_epi (σ.hom.app M')).mp h)

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The unit coherences of the comparisons of inverse images

These are the statements of `AlgebraicGeometry.Space.idComparison_comp_fac` and
`AlgebraicGeometry.Space.comp_idComparison_fac` for arbitrary morphisms of algebraic spaces in
place of morphisms of base changes, which is the generality the comparison of base changes below
needs; they belong beside those two.  Every statement is at the level of isomorphisms of
functors, never of their components, for the reason recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardCoherence.lean`. -/

/-- **The comparison of inverse images along a composite whose second factor is an identity is
the unit law `(𝟙 W)^* ≅ 𝟭`.**  This is the companion of
`AlgebraicGeometry.Space.ModulePushforwardCoherence.modulePullbackTriangle_id` for the other
factor. -/
theorem modulePullbackTriangle_comp_id (hc : ModulePushforwardCoherence B S hS)
    {V W : AlgebraicSpaces B S hS} {r : V ⟶ W} (hk : r ≫ 𝟙 W = r) :
    modulePullbackTriangle B S hS hk =
      (Functor.leftUnitor (modulePullback B S hS r)).symm ≪≫
        Functor.isoWhiskerRight (hc.modulePullbackIdIso W).symm (modulePullback B S hS r) := by
  have hE : modulePullbackTriangle B S hS hk =
      (modulePullbackCompIso B S hS r (𝟙 W)).symm := by
    rw [modulePullbackTriangle_eq]
    have h0 : eqToIso (congrArg (modulePullback B S hS) hk.symm) =
        eqToIso (congrArg (modulePullback B S hS) (rfl : r = r)) := rfl
    rw [h0]
    simp
  rw [hE, hc.modulePullbackCompIso_id_right r]
  simp [Functor.isoWhiskerRight_symm]

/-- Undoing the identification `𝟙 Z = e` and redoing it, between the unit law and itself, is the
identity. -/
private theorem modulePullbackIdIso_symm_eqToIso_trans_eqToIso_trans
    (hc : ModulePushforwardCoherence B S hS) {Z : AlgebraicSpaces B S hS} {e : Z ⟶ Z}
    (he : e = 𝟙 Z) :
    (((hc.modulePullbackIdIso Z).symm ≪≫ eqToIso (congrArg (modulePullback B S hS) he.symm)) ≪≫
        eqToIso (congrArg (modulePullback B S hS) he)) ≪≫ hc.modulePullbackIdIso Z =
      Iso.refl _ := by
  rw [Iso.trans_assoc (hc.modulePullbackIdIso Z).symm, eqToIso_trans, eqToIso_refl,
    Iso.trans_refl, Iso.symm_self_id]

/-- **A composite whose first factor is an identity.**  If the first factor of the composite is
an identity, composing the comparison of `AlgebraicGeometry.Space.modulePullbackTriangle` with
the unit law in that factor is the identification of the two inverse images induced by the
equality of morphisms. -/
theorem modulePullbackTriangle_id_left (hc : ModulePushforwardCoherence B S hS)
    {V Z : AlgebraicSpaces B S hS} {e : V ⟶ V} (he : e = 𝟙 V) {l : V ⟶ Z} {k : V ⟶ Z}
    (hk : e ≫ l = k) (hkl : k = l) :
    modulePullbackTriangle B S hS hk ≪≫
        Functor.isoWhiskerLeft (modulePullback B S hS l)
          (eqToIso (congrArg (modulePullback B S hS) he) ≪≫ hc.modulePullbackIdIso V) ≪≫
        Functor.rightUnitor (modulePullback B S hS l) =
      eqToIso (congrArg (modulePullback B S hS) hkl) := by
  have hk1 : 𝟙 V ≫ l = k := by rwa [← he]
  have hk2 : 𝟙 V ≫ l = l := Category.id_comp _
  rw [modulePullbackTriangle_congr_left he hk hk1, modulePullbackTriangle_congr hk1 hk2 hkl,
    hc.modulePullbackTriangle_id hk2]
  simp only [← Iso.trans_assoc, Functor.trans_isoWhiskerLeft_trans]
  rw [modulePullbackIdIso_symm_eqToIso_trans_eqToIso_trans hc he]
  simp

/-- **A composite whose second factor is an identity.**  If the second factor of the composite
is an identity, composing the comparison of `AlgebraicGeometry.Space.modulePullbackTriangle`
with the unit law in that factor is the identification of the two inverse images induced by the
equality of morphisms. -/
theorem modulePullbackTriangle_id_right (hc : ModulePushforwardCoherence B S hS)
    {V W : AlgebraicSpaces B S hS} {r : V ⟶ W} {q : W ⟶ W} (hq : q = 𝟙 W) {k : V ⟶ W}
    (hk : r ≫ q = k) (hkr : k = r) :
    modulePullbackTriangle B S hS hk ≪≫
        Functor.isoWhiskerRight
          (eqToIso (congrArg (modulePullback B S hS) hq) ≪≫ hc.modulePullbackIdIso W)
          (modulePullback B S hS r) ≪≫
        Functor.leftUnitor (modulePullback B S hS r) =
      eqToIso (congrArg (modulePullback B S hS) hkr) := by
  have hk1 : r ≫ 𝟙 W = k := by rwa [← hq]
  have hk2 : r ≫ 𝟙 W = r := Category.comp_id _
  rw [modulePullbackTriangle_congr_right hq hk hk1, modulePullbackTriangle_congr hk1 hk2 hkr,
    modulePullbackTriangle_comp_id hc hk2]
  simp only [← Iso.trans_assoc, Functor.trans_isoWhiskerRight_trans']
  rw [modulePullbackIdIso_symm_eqToIso_trans_eqToIso_trans hc hq]
  simp

/-- **The comparison of inverse images along a square whose two parallel sides are identities.**
If the two horizontal sides of the square are identities, the comparison of
`AlgebraicGeometry.Space.modulePullbackSquare` is the one the two unit laws induce. -/
theorem modulePullbackSquare_id (hc : ModulePushforwardCoherence B S hS)
    {V W : AlgebraicSpaces B S hS} {ε : V ⟶ W} {e : V ⟶ V} (he : e = 𝟙 V) {q : W ⟶ W}
    (hq : q = 𝟙 W) {k : V ⟶ W} (hk : e ≫ ε = k) (hk' : ε ≫ q = k) :
    modulePullbackSquare B S hS hk hk' ≪≫
        Functor.isoWhiskerRight
          (eqToIso (congrArg (modulePullback B S hS) hq) ≪≫ hc.modulePullbackIdIso W)
          (modulePullback B S hS ε) ≪≫
        Functor.leftUnitor (modulePullback B S hS ε) =
      Functor.isoWhiskerLeft (modulePullback B S hS ε)
          (eqToIso (congrArg (modulePullback B S hS) he) ≪≫ hc.modulePullbackIdIso V) ≪≫
        Functor.rightUnitor (modulePullback B S hS ε) := by
  have hkl : k = ε := by rw [← hk, he, Category.id_comp]
  have hkey : modulePullbackTriangle B S hS hk' ≪≫
        (Functor.isoWhiskerRight
            (eqToIso (congrArg (modulePullback B S hS) hq) ≪≫ hc.modulePullbackIdIso W)
            (modulePullback B S hS ε) ≪≫
          Functor.leftUnitor (modulePullback B S hS ε)) =
      modulePullbackTriangle B S hS hk ≪≫
        (Functor.isoWhiskerLeft (modulePullback B S hS ε)
            (eqToIso (congrArg (modulePullback B S hS) he) ≪≫ hc.modulePullbackIdIso V) ≪≫
          Functor.rightUnitor (modulePullback B S hS ε)) := by
    rw [modulePullbackTriangle_id_right hc hq hk' hkl,
      modulePullbackTriangle_id_left hc he hk hkl]
  calc modulePullbackSquare B S hS hk hk' ≪≫
        Functor.isoWhiskerRight
          (eqToIso (congrArg (modulePullback B S hS) hq) ≪≫ hc.modulePullbackIdIso W)
          (modulePullback B S hS ε) ≪≫
        Functor.leftUnitor (modulePullback B S hS ε)
      = (modulePullbackTriangle B S hS hk).symm ≪≫
          (modulePullbackTriangle B S hS hk' ≪≫
            (Functor.isoWhiskerRight
                (eqToIso (congrArg (modulePullback B S hS) hq) ≪≫ hc.modulePullbackIdIso W)
                (modulePullback B S hS ε) ≪≫
              Functor.leftUnitor (modulePullback B S hS ε))) := by
        simp only [modulePullbackSquare, Iso.trans_assoc]
    _ = (modulePullbackTriangle B S hS hk).symm ≪≫
          (modulePullbackTriangle B S hS hk ≪≫
            (Functor.isoWhiskerLeft (modulePullback B S hS ε)
                (eqToIso (congrArg (modulePullback B S hS) he) ≪≫ hc.modulePullbackIdIso V) ≪≫
              Functor.rightUnitor (modulePullback B S hS ε))) := by
        rw [hkey]
    _ = Functor.isoWhiskerLeft (modulePullback B S hS ε)
          (eqToIso (congrArg (modulePullback B S hS) he) ≪≫ hc.modulePullbackIdIso V) ≪≫
        Functor.rightUnitor (modulePullback B S hS ε) := by
        rw [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]

/-- Composing with an isomorphism and then with its inverse, in the left-associated bracketing,
does nothing. -/
private theorem trans_trans_symm {C : Type*} [Category* C] {X Y Z : C} (α : X ≅ Y) (β : Y ≅ Z) :
    (α ≪≫ β) ≪≫ β.symm = α := by
  rw [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]

/-- The associator of three composable functors is the identity: composition of functors is
associative on the nose. -/
private theorem associator_eq_refl {C : Type*} {D : Type*} {E : Type*} {F : Type*} [Category* C]
    [Category* D] [Category* E] [Category* F] (G : C ⥤ D) (H : D ⥤ E) (K : E ⥤ F) :
    Functor.associator G H K = Iso.refl _ := by
  apply Iso.ext
  ext X
  simp

/-- **The comparison of inverse images along a ladder of two squares.**  Two commuting squares
side by side, with the two horizontal composites named, give a third square; its comparison of
inverse images is the pasting of the two comparisons.

This is the associativity coherence of Stacks 03LU in the shape a consumer indexed by a category
of test objects needs for the functoriality of base change. -/
theorem modulePullbackSquare_comp (hc : ModulePushforwardCoherence B S hS)
    {V V' V'' W W' W'' : AlgebraicSpaces B S hS} {ε : V ⟶ W} {ε' : V' ⟶ W'} {ε'' : V'' ⟶ W''}
    {a : V ⟶ V'} {a' : V' ⟶ V''} {aa : V ⟶ V''} {b : W ⟶ W'} {b' : W' ⟶ W''} {bb : W ⟶ W''}
    (haa : a ≫ a' = aa) (hbb : b ≫ b' = bb) {km : V ⟶ W'} (hkm1 : a ≫ ε' = km)
    (hkm2 : ε ≫ b = km) {kn : V' ⟶ W''} (hkn1 : a' ≫ ε'' = kn) (hkn2 : ε' ≫ b' = kn)
    {k : V ⟶ W''} (hk1 : aa ≫ ε'' = k) (hk2 : ε ≫ bb = k) :
    modulePullbackSquare B S hS hk1 hk2 ≪≫
        Functor.isoWhiskerRight (modulePullbackTriangle B S hS hbb) (modulePullback B S hS ε) =
      Functor.isoWhiskerLeft (modulePullback B S hS ε'') (modulePullbackTriangle B S hS haa) ≪≫
        Functor.isoWhiskerRight (modulePullbackSquare B S hS hkn1 hkn2)
          (modulePullback B S hS a) ≪≫
        Functor.isoWhiskerLeft (modulePullback B S hS b')
          (modulePullbackSquare B S hS hkm1 hkm2) := by
  have hmb : km ≫ b' = k := by rw [← hkm2, Category.assoc, hbb, hk2]
  have han : a ≫ kn = k := by rw [← hkn1, ← Category.assoc, haa, hk1]
  have e1 := hc.modulePullbackTriangle_comp hkm2 hbb hk2 hmb
  have e2 := hc.modulePullbackTriangle_comp haa hkn1 han hk1
  have e3 := hc.modulePullbackTriangle_comp hkm1 hkn2 han hmb
  simp only [associator_eq_refl, Iso.trans_refl] at e1 e2 e3
  have key : modulePullbackTriangle B S hS hk1 ≪≫
      (Functor.isoWhiskerLeft (modulePullback B S hS ε'')
          (modulePullbackTriangle B S hS haa) ≪≫
        Functor.isoWhiskerRight (modulePullbackSquare B S hS hkn1 hkn2)
          (modulePullback B S hS a) ≪≫
        Functor.isoWhiskerLeft (modulePullback B S hS b')
          (modulePullbackSquare B S hS hkm1 hkm2)) =
      modulePullbackTriangle B S hS hk2 ≪≫
        Functor.isoWhiskerRight (modulePullbackTriangle B S hS hbb)
          (modulePullback B S hS ε) := by
    simp only [modulePullbackSquare, Functor.isoWhiskerRight_trans,
      Functor.isoWhiskerLeft_trans, ← Functor.isoWhiskerRight_symm,
      ← Functor.isoWhiskerLeft_symm, ← Iso.trans_assoc]
    rw [e2, trans_trans_symm, ← e3, trans_trans_symm, e1]
  rw [show modulePullbackSquare B S hS hk1 hk2 =
      (modulePullbackTriangle B S hS hk1).symm ≪≫ modulePullbackTriangle B S hS hk2 from rfl,
    Iso.trans_assoc, ← key, ← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]

/-- **A test scheme over `Y` is determined by its scheme and its morphism**: two of them joined
by a morphism whose underlying morphism of schemes is a transport are equal. -/
theorem schemesOver_eq_of_left_eqToHom {Y : AlgebraicSpaces B S hS} {u v : SchemesOver Y}
    (h : u.left = v.left) (m : u ⟶ v) (hm : m.left = eqToHom h) : u = v := by
  obtain ⟨uL, uR, uh⟩ := u
  obtain ⟨vL, vR, vh⟩ := v
  change uL = vL at h
  subst h
  have hw : (schemeSpaceFunctor B S hS).map m.left ≫ vh = uh := CostructuredArrow.w m
  rw [hm, eqToHom_refl, (schemeSpaceFunctor B S hS).map_id, Category.id_comp] at hw
  subst hw
  cases uR
  cases vR
  rfl

/-- **A vertical isomorphism of `𝒮_Y` is an identification.**  The fibres of `𝒮_Y` are sets, so a
morphism lying over an identity of the site identifies its source with its target. -/
theorem baseObjects_eq_of_vertical {Y : AlgebraicSpaces B S hS} {u v : BaseObjects Y}
    (m : u ⟶ v) {U : BigFppfOver B S hS}
    (hm : (baseBasedCategory Y).p.IsHomLift (𝟙 U) m) : u = v := by
  have hd : (ULiftHom.objDown u).left = U :=
    IsHomLift.domain_eq (baseBasedCategory Y).p (𝟙 U) m
  have hc : (ULiftHom.objDown v).left = U :=
    IsHomLift.codomain_eq (baseBasedCategory Y).p (𝟙 U) m
  refine schemesOver_eq_of_left_eqToHom (hd.trans hc.symm) m.down ?_
  change (baseBasedCategory Y).p.map m = eqToHom (hd.trans hc.symm)
  rw [IsHomLift.fac' (baseBasedCategory Y).p (𝟙 U) m]
  simp
  rfl

/-! ### Comparing two morphisms of `Coh_{X/Y}` -/

/-- **Two morphisms of `Coh_{X/Y}` with the same base map and the same comparison of modules are
equal**, the comparison of modules being compared heterogeneously.

This is `AlgebraicGeometry.Space.CoherentHom.ext` with the transport along the equality of base
maps replaced by a heterogeneous equality.  That is what makes it usable when the two base maps
are only definitionally equal: a transport would have to be recognised as an identity, and
recognising it forces the underlying morphism of a comparison of inverse images to be computed,
which is what the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardCoherence.lean` record as
intractable. -/
theorem coherentHom_eq_of_heq {D : CoherentSituation B S hS} {A A' : CoherentObject D}
    {m n : CoherentHom A A'} (hb : m.base = n.base) (h : HEq m.fibre n.fibre) : m = n := by
  obtain ⟨mb, mf, mi⟩ := m
  obtain ⟨nb, nf, ni⟩ := n
  change mb = nb at hb
  subst hb
  cases eq_of_heq h
  rfl

/-- **Two equal morphisms of `Coh_{X/Y}` carry the same comparison of modules**, heterogeneously:
their comparisons have the same type only once the base maps are identified, so the conclusion is
a heterogeneous equality.  This is the converse of
`AlgebraicGeometry.Space.coherentHom_eq_of_heq`. -/
theorem heq_fibre_of_eq {D : CoherentSituation B S hS} {A A' : CoherentObject D}
    {m n : CoherentHom A A'} (h : m = n) : HEq m.fibre n.fibre := by
  subst h
  rfl

namespace CoherentHom

variable {D : CoherentSituation B S hS}

/-- The comparison of modules of the identity of `Coh_{X/Y}` is the unit law of Stacks 03LU. -/
theorem id_fibre (hc : ModulePushforwardCoherence B S hS) (A : CoherentObject D) :
    (CoherentHom.id hc A).fibre = (D.idComparison hc A.T).hom.app A.F :=
  rfl

/-- The comparison of modules of a composite of `Coh_{X/Y}` is the composite of the two
comparisons along the comparison of Stacks 03LU for the composite. -/
theorem comp_fibre {A A' A'' : CoherentObject D} (m : CoherentHom A A')
    (n : CoherentHom A' A'') :
    (m.comp n).fibre = Functor.fibreComp (D.compComparison m.base n.base) m.fibre n.fibre :=
  rfl

end CoherentHom

namespace CoherentSituation

variable (D : CoherentSituation B S hS) {Y' : AlgebraicSpaces B S hS}

/-! ### The base-changed standing datum -/

/-- **The base change of the standing data of Stacks 08KB.**  For a morphism `g : Y' ⟶ Y` of
algebraic spaces the projection `f' : X ×_Y Y' ⟶ Y'` is again of finite presentation, finite
presentation being stable under base change (Stacks 03XR), so it is again a standing datum. -/
def baseChange (g : Y' ⟶ D.Y) : CoherentSituation B S hS where
  X := AlgebraicSpaces.fiberProduct B S hS D.f g
  Y := Y'
  f := ObjectProperty.homMk (pullback.snd D.f.hom g.hom)
  finitePresentation :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) => IsFinitePresentation B S hS k.hom)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f g) D.finitePresentation

/-- The base of the base-changed standing datum is the new base. -/
theorem baseChange_Y (g : Y' ⟶ D.Y) : (D.baseChange g).Y = Y' :=
  rfl

/-- A test scheme over `Y'`, read as a test scheme over `Y` by composing with `g`. -/
abbrev overBase (g : Y' ⟶ D.Y) : SchemesOver (D.baseChange g).Y ⥤ SchemesOver D.Y :=
  CostructuredArrow.map g

/-- Reading a morphism of test schemes over `Y'` as one over `Y` does not change the underlying
morphism of schemes of the site. -/
@[simp]
theorem overBase_map_left (g : Y' ⟶ D.Y) {T T' : SchemesOver (D.baseChange g).Y} (h : T ⟶ T') :
    ((D.overBase g).map h).left = h.left :=
  rfl

/-! ### The comparison of the two base changes -/

/-- **The comparison `X'_T ≅ X_T`.**  The base change of `X' = X ×_Y Y'` to a test scheme `T`
over `Y'` is the iterated fibre product `(X ×_Y Y') ×_{Y'} T`, which the pasting isomorphism
identifies with the base change `X ×_Y T` of `X` to `T` read as a test scheme over `Y`. -/
def baseChangeSpaceIso (g : Y' ⟶ D.Y) (T : SchemesOver (D.baseChange g).Y) :
    baseChangeSpace (D.baseChange g).f T ≅ baseChangeSpace D.f ((D.overBase g).obj T) :=
  ObjectProperty.isoMk _ (pullbackLeftPullbackSndIso D.f.hom g.hom T.hom.hom)

/-- The comparison commutes with the projections to the test scheme. -/
@[reassoc]
theorem baseChangeSpaceIso_hom_inclusion (g : Y' ⟶ D.Y) (T : SchemesOver (D.baseChange g).Y) :
    (D.baseChangeSpaceIso g T).hom ≫ baseChangeInclusion D.f ((D.overBase g).obj T) =
      baseChangeInclusion (D.baseChange g).f T :=
  ObjectProperty.hom_ext _ (pullbackLeftPullbackSndIso_hom_snd D.f.hom g.hom T.hom.hom)

/-- The comparison commutes with the projections to the source, up to the projection
`X ×_Y Y' ⟶ X`. -/
@[reassoc]
theorem baseChangeSpaceIso_hom_projection (g : Y' ⟶ D.Y) (T : SchemesOver (D.baseChange g).Y) :
    (D.baseChangeSpaceIso g T).hom ≫ baseChangeProjection D.f ((D.overBase g).obj T) =
      baseChangeProjection (D.baseChange g).f T ≫
        ObjectProperty.homMk (pullback.fst D.f.hom g.hom) :=
  ObjectProperty.hom_ext _ (pullbackLeftPullbackSndIso_hom_fst D.f.hom g.hom T.hom.hom)

/-- **The comparison is natural in the test scheme.** -/
theorem baseChangeSpaceIso_naturality (g : Y' ⟶ D.Y)
    {T T' : SchemesOver (D.baseChange g).Y} (h : T ⟶ T') :
    baseChangeMap (D.baseChange g).f h ≫ (D.baseChangeSpaceIso g T').hom =
      (D.baseChangeSpaceIso g T).hom ≫ baseChangeMap D.f ((D.overBase g).map h) := by
  refine baseChange_hom_ext D.f ?_ ?_
  · simp only [Category.assoc, baseChangeSpaceIso_hom_projection,
      baseChangeMap_comp_projection]
    exact congrArg (fun k => k ≫ ObjectProperty.homMk (pullback.fst D.f.hom g.hom))
      (baseChangeMap_comp_projection (D.baseChange g).f h)
  · simp only [Category.assoc, baseChangeSpaceIso_hom_inclusion,
      baseChangeSpaceIso_hom_inclusion_assoc, baseChangeMap_comp_inclusion,
      overBase_map_left]

/-- **The comparison sits in a cartesian square over the identity of the test scheme.**  This is
the square at which the base-change stability of the conditions defining an object of
`Coh_{X/Y}` is applied to transport a module along the comparison. -/
theorem isPullback_baseChangeSpaceIso_inv (g : Y' ⟶ D.Y) (T : SchemesOver (D.baseChange g).Y) :
    IsPullback (D.baseChangeSpaceIso g T).inv (baseChangeInclusion D.f ((D.overBase g).obj T))
      (baseChangeInclusion (D.baseChange g).f T) (𝟙 _) := by
  have hsq : (D.baseChangeSpaceIso g T).inv ≫ baseChangeInclusion (D.baseChange g).f T =
      baseChangeInclusion D.f ((D.overBase g).obj T) := by
    rw [← baseChangeSpaceIso_hom_inclusion D g T, Iso.inv_hom_id_assoc]
  exact IsPullback.of_horiz_isIso (CommSq.mk (by simpa using hsq))

/-- The comparison, read with its inverse, is natural in the test scheme. -/
theorem baseChangeSpaceIso_inv_naturality (g : Y' ⟶ D.Y)
    {T T' : SchemesOver (D.baseChange g).Y} (h : T ⟶ T') :
    (D.baseChangeSpaceIso g T).inv ≫ baseChangeMap (D.baseChange g).f h =
      baseChangeMap D.f ((D.overBase g).map h) ≫ (D.baseChangeSpaceIso g T').inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← baseChangeSpaceIso_naturality D g h,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-! ### The comparison of the two iterated inverse images -/

/-- **The comparison of the two iterated inverse images along the square of a morphism of test
schemes.**  The comparison `X_T ⟶ X'_T` and the morphisms of base changes induced by a morphism
`h : T ⟶ T'` of test schemes form a commuting square, and this is the comparison of Stacks 03LU
for its two sides. -/
def baseChangeModuleSquare (g : Y' ⟶ D.Y)
    {T T' : SchemesOver (D.baseChange g).Y} (h : T ⟶ T') :
    modulePullback B S hS (D.baseChangeSpaceIso g T').inv ⋙
        modulePullback B S hS (baseChangeMap D.f ((D.overBase g).map h)) ≅
      modulePullback B S hS (baseChangeMap (D.baseChange g).f h) ⋙
        modulePullback B S hS (D.baseChangeSpaceIso g T).inv :=
  modulePullbackSquare B S hS rfl (D.baseChangeSpaceIso_inv_naturality g h)

variable (hc : ModulePushforwardCoherence B S hS)

/-- **The comparison of base changes is compatible with the unit law of Stacks 03LU.** -/
theorem baseChangeModuleSquare_id (g : Y' ⟶ D.Y) (T : SchemesOver (D.baseChange g).Y) :
    D.baseChangeModuleSquare g (𝟙 T) ≪≫
        Functor.isoWhiskerRight ((D.baseChange g).idComparison hc T)
          (modulePullback B S hS (D.baseChangeSpaceIso g T).inv) ≪≫
        Functor.leftUnitor (modulePullback B S hS (D.baseChangeSpaceIso g T).inv) =
      Functor.isoWhiskerLeft (modulePullback B S hS (D.baseChangeSpaceIso g T).inv)
          (D.idComparison hc ((D.overBase g).obj T)) ≪≫
        Functor.rightUnitor (modulePullback B S hS (D.baseChangeSpaceIso g T).inv) :=
  modulePullbackSquare_id hc (baseChangeMap_id D.f ((D.overBase g).obj T))
    (baseChangeMap_id (D.baseChange g).f T) rfl
    (D.baseChangeSpaceIso_inv_naturality g (𝟙 T))

/-- The comparison of base changes at the base map of an identity. -/
theorem baseChangeModuleSquare_idBase (g : Y' ⟶ D.Y)
    (A : CoherentObject (D.baseChange g)) :
    D.baseChangeModuleSquare g (CoherentHom.id hc A).base =
      D.baseChangeModuleSquare g (𝟙 A.T) :=
  rfl

/-- The comparison of base changes at the base map of a composite. -/
theorem baseChangeModuleSquare_compBase (g : Y' ⟶ D.Y)
    {A A' A'' : CoherentObject (D.baseChange g)} (m : CoherentHom A A')
    (n : CoherentHom A' A'') :
    D.baseChangeModuleSquare g (m.comp n).base =
      D.baseChangeModuleSquare g (m.base ≫ n.base) :=
  rfl

/-- The comparison of base changes at a composite of morphisms of test schemes, presented with
the composite of the two induced morphisms of base changes written out.  This is the shape the
pasting law `AlgebraicGeometry.Space.modulePullbackSquare_comp` produces. -/
theorem baseChangeModuleSquare_comp_eq (g : Y' ⟶ D.Y) {T T' T'' : SchemesOver (D.baseChange g).Y}
    (h : T ⟶ T') (h' : T' ⟶ T'') :
    D.baseChangeModuleSquare g (h ≫ h') =
      modulePullbackSquare B S hS
        (rfl : baseChangeMap D.f ((D.overBase g).map h ≫ (D.overBase g).map h') ≫
          (D.baseChangeSpaceIso g T'').inv = _)
        (D.baseChangeSpaceIso_inv_naturality g (h ≫ h')) :=
  rfl

/-! ### Full faithfulness of the inverse image along the comparison -/

/-- **The comparison, read with its forward map, sits in a cartesian square over the identity.** -/
theorem isPullback_baseChangeSpaceIso_hom (g : Y' ⟶ D.Y)
    (T : SchemesOver (D.baseChange g).Y) :
    IsPullback (D.baseChangeSpaceIso g T).hom (baseChangeInclusion (D.baseChange g).f T)
      (baseChangeInclusion D.f ((D.overBase g).obj T)) (𝟙 _) :=
  IsPullback.of_horiz_isIso
    (CommSq.mk (by simpa using D.baseChangeSpaceIso_hom_inclusion g T))

/-- **The inverse image along the comparison of base changes is fully faithful**, the comparison
being an isomorphism. -/
def fullyFaithful_modulePullback_baseChangeSpaceIso
    (hc : ModulePushforwardCoherence B S hS) (g : Y' ⟶ D.Y)
    (T : SchemesOver (D.baseChange g).Y) :
    (modulePullback B S hS (D.baseChangeSpaceIso g T).inv).FullyFaithful :=
  (hc.modulePullbackEquivalence (D.baseChangeSpaceIso g T).symm).fullyFaithfulFunctor

end CoherentSituation

end AlgebraicGeometry.Space

end
