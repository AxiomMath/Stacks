module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
import StacksFrontier.AlgebraicGeometry.FormalSpace.FpqcSheafGlueing
import StacksFrontier.CategoryTheory.Sites.Density

/-!
# Rig-surjectivity of a monomorphism of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`, and let `f : X ⟶ Y` be a morphism of
locally Noetherian formal algebraic spaces over `S` which is locally of finite type and a
monomorphism. Then `f` is rig-surjective (Stacks 0AQQ) exactly when every adic morphism
`Spf R ⟶ Y` out of the formal spectrum of a complete discrete valuation ring factors through
`X` — with no extension of `R` needed. This is **Stacks 0AR0**.

## Main definitions

* `AlgebraicGeometry.FormalSpace.FactorsAdicCompleteDvrPoints`: the right-hand side of
  Stacks 0AR0, the factorisation criterion over the complete discrete valuation ring itself.

## Main results

* `AlgebraicGeometry.FormalSpace.isRigSurjective_of_factorsAdicCompleteDvrPoints`: the
  direction the source calls trivial.
* `AlgebraicGeometry.FormalSpace.factorsAdicCompleteDvrPoints_of_isRigSurjective`: the
  substantial direction.
* `AlgebraicGeometry.FormalSpace.isRigSurjective_iff_factorsAdicCompleteDvrPoints`:
  **Stacks 0AR0**, the equivalence.

## Implementation notes

The factorisation criterion is spelled with the same quantifier interface as
`AlgebraicGeometry.FormalSpace.IsRigSurjective`: the complete discrete valuation ring `R` is
presented over `S` by an `AlgebraicGeometry.FormalSpace.QuotientSystem`, completeness is
`IsAdicComplete` for the maximal ideal whose adic topology is the one `R` carries, weak
admissibility of that topology is quantified over rather than derived because it is what
`AlgebraicGeometry.FormalSpace.formalSpectrumMap` consumes, and adicness of the point is
rendered by representability by algebraic spaces, which **Stacks 0AQ3** identifies with
adicness for a morphism of locally adic\* formal algebraic spaces. The factorisation is
produced as an `∃`, never chosen: nothing downstream of Stacks 0AR0 needs a selected lift.

The direction the source calls trivial takes `R' = R`, for which the extension condition of
Stacks 09E4 and the identity continuous homomorphism are available, and
`AlgebraicGeometry.FormalSpace.formalSpectrumMap_id` turns the vertical map of formal spectra
into the identity, so the factorisation asked for by rig-surjectivity is the given one.

The substantial direction is the source's descent argument. Given a lift `Spf R' ⟶ X` of
`p : Spf R ⟶ Y` along an extension `R ⊂ R'` of complete discrete valuation rings, each weak
ideal of definition `J` of `R` has `J R'` a weak ideal of definition of `R'`
(`weakIdealOfDefinition_map`, using that the maximal ideal of `R` generates a power of the
maximal ideal of `R'`), and `R/J → R'/J R'` is faithfully flat
(`faithfullyFlat_quotientMap`, from flatness of `R'` over the discrete valuation ring `R`
together with locality of the extension), so `Spec (R'/J R') ⟶ Spec (R/J)` is a one-element
fpqc covering. The section of `Y` over `Spec (R/J)` cut out by `p` and the section of `X` over
`Spec (R'/J R')` cut out by the lift then agree over the covering, so the latter descends to a
section of `X` over `Spec (R/J)` mapping to the former, because `X` and `Y` are fpqc sheaves
and `f` is injective on sections. Monomorphy of `f` makes those descended sections compatible
with the transition maps of the quotient system, hence a cocone on the colimit diagram
defining `Spf R`, and the induced map `Spf R ⟶ X` is the factorisation wanted.

Descent of a section along a one-element covering is isolated as `exists_descended_section`,
which is a statement about an objectwise injective morphism of type-valued sheaves for an
arbitrary precoverage and uses nothing about formal algebraic spaces.

### The input from Stacks 0AQD

The substantial direction uses that `X` and `Y` satisfy the sheaf condition for fpqc coverings of
the schemes of the site, which is **Stacks 0AQD**,
`AlgebraicGeometry.FormalSpace.isSheaf_fpqc`. The locally Noetherian hypotheses on `X` and `Y`
enter the proof only by making `X` and `Y` formal algebraic spaces, so that Stacks 0AQD applies;
they are kept, rather than weakened to Stacks 0AIM, because they are the hypotheses of
Stacks 0AR0.

The locally finite type hypothesis on `f` is likewise a hypothesis of Stacks 0AR0 and is kept,
although neither direction uses it: `AlgebraicGeometry.FormalSpace.IsRigSurjective` is the
quantified lifting condition alone, with the standing hypotheses of Stacks 0AQQ imposed by its
consumers, so there is nothing for it to discharge here.

## References

* [Stacks Project, Tag 09E4](https://stacks.math.columbia.edu/tag/09E4)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AKY](https://stacks.math.columbia.edu/tag/0AKY)
* [Stacks Project, Tag 0AMV](https://stacks.math.columbia.edu/tag/0AMV)
* [Stacks Project, Tag 0AQ3](https://stacks.math.columbia.edu/tag/0AQ3)
* [Stacks Project, Tag 0AQB](https://stacks.math.columbia.edu/tag/0AQB)
* [Stacks Project, Tag 0AQD](https://stacks.math.columbia.edu/tag/0AQD)
* [Stacks Project, Tag 0AQQ](https://stacks.math.columbia.edu/tag/0AQQ)
* [Stacks Project, Tag 0AR0](https://stacks.math.columbia.edu/tag/0AR0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.FormalSpace

/-! ### Descent along a one-element covering -/

section Descent

universe w₀ v₀ u₀

/-- Sections of a type-valued sheaf descend along a one-element covering when their images
under an objectwise injective morphism of sheaves descend: the given section is its own
compatible family for that covering, so it amalgamates, and the amalgamation has the
prescribed image because the target is separated. -/
private theorem exists_descended_section {C : Type u₀} [Category.{w₀, u₀} C]
    (Q : Precoverage C) (F G : Cᵒᵖ ⥤ Type v₀) (α : F ⟶ G)
    (hα : ∀ U : C, Function.Injective (α.app (op U)))
    (hF : Presheaf.IsSheaf Q.toGrothendieck F) (hG : Presheaf.IsSheaf Q.toGrothendieck G)
    {U V : C} (g : V ⟶ U) (hcover : Presieve.singleton g ∈ Q U)
    (x : F.obj (op V)) (y : G.obj (op U)) (hxy : α.app (op V) x = G.map g.op y) :
    ∃ z : F.obj (op U), F.map g.op z = x ∧ α.app (op U) z = y := by
  let E : Type v₀ := PUnit.{v₀ + 1}
  let e₀ : E := PUnit.unit
  let i₀ : PUnit.{w₀ + 1} := PUnit.unit
  let W : PUnit.{w₀ + 1} → C := fun _ ↦ V
  let q : ∀ i, W i ⟶ U := fun _ ↦ g
  have hpre : Presieve.ofArrows W q ∈ Q U := by rwa [Presieve.ofArrows_pUnit]
  have hcov : Sieve.ofArrows W q ∈ Q.toGrothendieck U :=
    Precoverage.generate_mem_toGrothendieck hpre
  let localX : ∀ i, E ⟶ F.obj (op (W i)) := fun _ ↦ TypeCat.ofHom fun (_ : E) ↦ x
  have hlocalX : ∀ ⦃Z : C⦄ ⦃i j : PUnit.{w₀ + 1}⦄ (a : Z ⟶ W i) (b : Z ⟶ W j),
      a ≫ q i = b ≫ q j → localX i ≫ F.map a.op = localX j ≫ F.map b.op := by
    intro Z i j a b hab
    ext z
    apply hα Z
    have key (c : Z ⟶ V) : α.app (op Z) (F.map c.op x) = G.map (c ≫ g).op y := by
      rw [NatTrans.naturality_apply, hxy, op_comp, Functor.map_comp_apply]
    change α.app (op Z) (F.map a.op x) = α.app (op Z) (F.map b.op x)
    rw [key, key, hab]
  let zHom := hF.amalgamateOfArrows q hcov localX hlocalX
  have hz : F.map g.op (zHom e₀) = x := congrArg (fun m : E ⟶ F.obj (op V) ↦ m e₀)
    (hF.amalgamateOfArrows_map q hcov localX hlocalX i₀)
  refine ⟨zHom e₀, hz, ?_⟩
  have hrestrict : G.map g.op (α.app (op U) (zHom e₀)) = G.map g.op y := by
    calc G.map g.op (α.app (op U) (zHom e₀)) = α.app (op V) (F.map g.op (zHom e₀)) :=
          (NatTrans.naturality_apply α g.op (zHom e₀)).symm
      _ = α.app (op V) x := congrArg _ hz
      _ = G.map g.op y := hxy
  have heq : (TypeCat.ofHom fun (_ : E) ↦ α.app (op U) (zHom e₀)) =
      (TypeCat.ofHom fun (_ : E) ↦ y) := by
    refine hG.hom_ext_ofArrows q hcov fun i ↦ ?_
    ext a
    exact hrestrict
  exact congrArg (fun m : E ⟶ G.obj (op U) ↦ m e₀) heq

end Descent

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Two facts about an extension of complete discrete valuation rings -/

/-- The image of a weak ideal of definition of `R` under an extension `R ⊂ R'` of discrete
valuation rings carrying their maximal-adic topologies is a weak ideal of definition of `R'`:
the maximal ideal of `R` generates the `e`-th power of that of `R'`, so a power of the maximal
ideal of `R'` lands inside the image, which is therefore open, and its elements are
topologically nilpotent because they are continuous images of topologically nilpotent
elements. -/
private theorem weakIdealOfDefinition_map {R R' : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsDiscreteValuationRing.IsExtension R R'] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R] [TopologicalSpace R'] [IsTopologicalRing R']
    [IsLinearTopology R' R'] (hR : _root_.IsAdic (IsLocalRing.maximalIdeal R))
    (hR' : _root_.IsAdic (IsLocalRing.maximalIdeal R')) (φ : R →+* R') (hφ : φ = algebraMap R R')
    (hcont : Continuous φ) (J : Ideal R)
    (hJ : TopologicalRing.IsWeakIdealOfDefinition J) :
    TopologicalRing.IsWeakIdealOfDefinition (J.map φ) := by
  obtain ⟨n, hn⟩ := (isAdic_iff.mp hR).2 (J : Set R) (hJ.1.mem_nhds J.zero_mem)
  obtain ⟨-, hpow, -, -⟩ := IsDiscreteValuationRing.ramificationIndex_characterization R R'
  set e := IsDiscreteValuationRing.ramificationIndex R R' with he
  have hmap : (IsLocalRing.maximalIdeal R).map φ = IsLocalRing.maximalIdeal R' ^ e := by
    simpa [hφ, he] using hpow
  have hle : IsLocalRing.maximalIdeal R' ^ (e * n) ≤ J.map φ := by
    rw [pow_mul, ← hmap, ← Ideal.map_pow]
    exact Ideal.map_mono (SetLike.coe_subset_coe.mp hn)
  have hnhds : (J.map φ : Set R') ∈ nhds (0 : R') :=
    Filter.mem_of_superset
      ((isAdic_iff.mp hR').1 (e * n) |>.mem_nhds
        (IsLocalRing.maximalIdeal R' ^ (e * n)).zero_mem)
      (SetLike.coe_subset_coe.mpr hle)
  refine ⟨(J.map φ).toAddSubgroup.isOpen_of_mem_nhds hnhds, fun x hx ↦ ?_⟩
  have hnil : J.map φ ≤ topologicalNilradical R' := by
    rw [Ideal.map_le_iff_le_comap]
    exact fun y hy ↦ (hJ.2 y hy).map hcont
  exact IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp (hnil hx)

/-- For an extension `R ⊂ R'` of discrete valuation rings and an ideal `J` of `R`, the induced
map `R/J → R'/J R'` is faithfully flat: `R'` is torsion-free over the Bézout domain `R` and the
extension is local, so `R'` is faithfully flat over `R`, and `R'/J R'` is the base change of
`R'` along `R → R/J`. -/
private theorem faithfullyFlat_quotientMap {R R' : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsDiscreteValuationRing.IsExtension R R'] (J : Ideal R) :
    RingHom.FaithfullyFlat
      (Ideal.quotientMap (J.map (algebraMap R R')) (algebraMap R R') Ideal.le_comap_map) := by
  have : Module.Flat R R' := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
      ← Submodule.isTorsionFree_iff_torsion_eq_bot, Module.isTorsionFree_iff_smul_eq_zero]
    intro a b hab
    rw [Algebra.smul_def] at hab
    exact (mul_eq_zero.mp hab).imp_left fun h ↦
      FaithfulSMul.algebraMap_injective R R' (by simpa using h)
  have : Module.FaithfullyFlat R R' := Module.FaithfullyFlat.of_flat_of_isLocalHom
  change RingHom.FaithfullyFlat (algebraMap (R ⧸ J) (R' ⧸ J.map (algebraMap R R')))
  exact RingHom.faithfullyFlat_algebraMap_iff.mpr <|
    Module.FaithfullyFlat.of_linearEquiv (R ⧸ J) ((R ⧸ J) ⊗[R] R')
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor R' J).toLinearEquiv

/-! ### Monomorphy on sections -/

/-- **Stacks 0AQB.** A monomorphism of fppf sheaves on the big fppf site of `S` is injective
on sections over every object of the site: two sections with the same image give two morphisms
out of the sheafified representable with the same composite with the monomorphism, hence agree,
and Yoneda's lemma for sheaves of sets is a bijection. -/
private theorem app_injective_of_mono {X Y : FppfSheaf B S hS} (f : X ⟶ Y) [Mono f]
    (T : BigFppfOver B S hS) : Function.Injective (f.hom.app (op T)) := by
  intro a b hab
  let J := BigFppfOver.topology B S hS
  have hmor : (Sheaf.sectionEquiv J).symm a ≫ f = (Sheaf.sectionEquiv J).symm b ≫ f := by
    apply (Sheaf.sectionEquiv J).injective
    rwa [Sheaf.sectionEquiv_comp, Equiv.apply_symm_apply, Sheaf.sectionEquiv_comp,
      Equiv.apply_symm_apply]
  exact (Sheaf.sectionEquiv J).symm.injective ((cancel_mono f).1 hmor)

/-! ### The factorisation criterion -/

/-- The right-hand side of **Stacks 0AR0**: every adic morphism to `Y` out of the formal
spectrum of a complete discrete valuation ring `R` factors through `X`, over `R` itself rather
than over an extension of it. The quantifier interface is that of
`AlgebraicGeometry.FormalSpace.IsRigSurjective`, with the factorisation asserted to exist. -/
abbrev FactorsAdicCompleteDvrPoints {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R],
    _root_.IsAdic (IsLocalRing.maximalIdeal R) → IsAdicComplete (IsLocalRing.maximalIdeal R) R →
      ∀ (_hR : TopologicalRing.IsWeaklyAdmissible R) (D : QuotientSystem B S hS R)
        (p : formalSpectrum D ⟶ Y),
        Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS p.hom →
          ∃ x : formalSpectrum D ⟶ X, x ≫ f = p

/-- The direction of **Stacks 0AR0** the source calls trivial, for an arbitrary morphism of fppf
sheaves on the big fppf site of `S`. If every adic point of `Y` out of the formal spectrum of a
complete discrete valuation ring `R` factors through `X` over `R` itself, then `f` is
rig-surjective: take the extension of `R` asked for by rig-surjectivity to be `R` itself, whose
formal-spectrum map is the identity by Stacks 0AIF. Neither the hypotheses of Stacks 0AR0 nor
monomorphy of `f` is needed. -/
theorem isRigSurjective_of_factorsAdicCompleteDvrPoints {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hfactor : FactorsAdicCompleteDvrPoints B S hS f) : IsRigSurjective B S hS f := by
  intro R _ _ _ _ _ _ hRadic hRcomplete hRweak D p hp
  obtain ⟨x, hx⟩ := hfactor R hRadic hRcomplete hRweak D p hp
  have : IsDiscreteValuationRing.IsExtension R R := ⟨⟩
  let e : ContinuousHom D D :=
    { toRingHom := RingHom.id R
      continuous := continuous_id
      overS := by
        intro J K h
        have hJK : J.1 ≤ K.1 := by simpa using h
        have hq : Ideal.quotientMap K.1 (RingHom.id R) h = Ideal.Quotient.factor hJK := by
          refine RingHom.ext fun z ↦ ?_
          obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
          simp [Ideal.quotientMap_mk]
        change Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 (RingHom.id R) h)) ≫
          D.overS J = D.overS K
        rw [hq]
        exact D.compatible J K hJK }
  exact ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, hRadic, hRcomplete, D, e, x, rfl,
    by simpa [formalSpectrumMap_id hRweak e rfl] using hx⟩

/-- The substantial direction of **Stacks 0AR0**. Let `f : X ⟶ Y` be a
monomorphism of locally Noetherian formal algebraic spaces over `S` which is locally of finite
type. If `f` is rig-surjective then every adic point of `Y` out of the formal spectrum of a
complete discrete valuation ring `R` factors through `X` over `R` itself.

Rig-surjectivity provides an extension `R ⊂ R'` of complete discrete valuation rings and a
lift `Spf R' ⟶ X` of the point. For each weak ideal of definition `J` of `R` the morphism
`Spec (R'/J R') ⟶ Spec (R/J)` is a one-element fpqc covering, so the section of `X` over
`Spec (R'/J R')` cut out by the lift descends to a section over `Spec (R/J)` mapping to the
section of `Y` cut out by the point. Monomorphy of `f` makes the descended sections a cocone on
the colimit diagram defining `Spf R`, whose induced map is the factorisation.

That `X` and `Y` are fpqc sheaves is Stacks 0AQD, `AlgebraicGeometry.FormalSpace.isSheaf_fpqc`. -/
theorem factorsAdicCompleteDvrPoints_of_isRigSurjective {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y)
    (_hft : IsLocallyOfFiniteType B S hS f) [Mono f]
    (hrig : IsRigSurjective B S hS f) : FactorsAdicCompleteDvrPoints B S hS f := by
  intro R _ _ _ _ _ _ hRadic hRcomplete hRweak D p hp
  obtain ⟨R', _, _, _, _, _, _, _, _, hR'adic, -, D', e, xext, he, hfac⟩ :=
    hrig R hRadic hRcomplete hRweak D p hp
  let JIndex := { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }
  let K : JIndex → { I : Ideal R' // TopologicalRing.IsWeakIdealOfDefinition I } := fun J ↦
    ⟨J.1.map (algebraMap R R'),
      weakIdealOfDefinition_map hRadic hR'adic (algebraMap R R') rfl
        (by simpa [← he] using e.continuous) J.1 J.2⟩
  have hIdeal : ∀ J : JIndex, J.1 ≤ Ideal.comap e.toRingHom (K J).1 := fun J ↦
    he ▸ Ideal.le_comap_map
  let U : JIndex → BigFppfOver B S hS := fun J ↦
    (BigAffineFppf.inclusion B S hS).obj (D.stage J)
  let V : JIndex → BigFppfOver B S hS := fun J ↦
    (BigAffineFppf.inclusion B S hS).obj (D'.stage (K J))
  let g : ∀ J : JIndex, V J ⟶ U J := fun J ↦
    (BigAffineFppf.inclusion B S hS).map (e.stageMap J (K J) (hIdeal J))
  let T := BigFppfOver.toScheme B S hS
  have hcover : ∀ J : JIndex,
      Presieve.singleton (T.map (g J)) ∈ Scheme.fpqcPrecoverage (T.obj (U J)) := by
    intro J
    have hqmap : Ideal.quotientMap (K J).1 e.toRingHom (hIdeal J) =
        Ideal.quotientMap (K J).1 (algebraMap R R') Ideal.le_comap_map := by
      refine RingHom.ext fun z ↦ ?_
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
      simp [Ideal.quotientMap_mk, he]
    let q := CommRingCat.ofHom (Ideal.quotientMap (K J).1 e.toRingHom (hIdeal J))
    have hff : RingHom.FaithfullyFlat
        (Ideal.quotientMap (K J).1 e.toRingHom (hIdeal J)) := by
      rw [hqmap]; exact faithfullyFlat_quotientMap J.1
    obtain ⟨_, _⟩ := (flat_and_surjective_SpecMap_iff q).2 hff
    change Presieve.singleton (Spec.map q) ∈ Scheme.fpqcPrecoverage (Spec (.of (R ⧸ J.1)))
    exact (Spec.map q).singleton_mem_fpqcPrecoverage
  let Jsite := BigFppfOver.topology B S hS
  let yStage : ∀ J : JIndex, (Sheaf.sheafifiedYoneda Jsite).obj (U J) ⟶ Y := fun J ↦
    formalSpectrumInclusion D (OrderDual.toDual J) ≫ p
  let xStage : ∀ J : JIndex, (Sheaf.sheafifiedYoneda Jsite).obj (V J) ⟶ X := fun J ↦
    formalSpectrumInclusion D' (OrderDual.toDual (K J)) ≫ xext
  have hxy : ∀ J : JIndex, f.hom.app (op (V J)) (Sheaf.sectionEquiv Jsite (xStage J)) =
      Y.obj.map (g J).op (Sheaf.sectionEquiv Jsite (yStage J)) := fun J ↦ by
    have h : xStage J ≫ f = (Sheaf.sheafifiedYoneda Jsite).map (g J) ≫ yStage J := by
      dsimp only [xStage, yStage]
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun q ↦ formalSpectrumInclusion D' (OrderDual.toDual (K J)) ≫ q) hfac).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun q ↦ q ≫ p)
              (formalSpectrumMap_spec hRweak e J (K J) (hIdeal J))).trans (Category.assoc _ _ _))))
    have h := congrArg (Sheaf.sectionEquiv Jsite) h
    rwa [Sheaf.sectionEquiv_comp, Sheaf.sectionEquiv_map_comp] at h
  choose z hz using fun J : JIndex ↦
    (exists_descended_section (Scheme.fpqcPrecoverage.comap T) X.obj Y.obj f.hom
      (app_injective_of_mono B S hS f) (isSheaf_fpqc hX.1) (isSheaf_fpqc hY.1) (g J)
      (by simpa [Precoverage.mem_comap_iff] using hcover J) _ _ (hxy J)).imp fun _ ↦ And.right
  let xMap : ∀ J : JIndex, (Sheaf.sheafifiedYoneda Jsite).obj (U J) ⟶ X := fun J ↦
    (Sheaf.sectionEquiv Jsite).symm (z J)
  have hmapFactor : ∀ J : JIndex, xMap J ≫ f = yStage J := fun J ↦
    (Sheaf.sectionEquiv Jsite).injective <| by
      rw [Sheaf.sectionEquiv_comp, Equiv.apply_symm_apply]
      exact hz J
  let c : Cocone (formalSpectrumDiagram D) :=
    { pt := X
      ι :=
        { app := fun j ↦ xMap (OrderDual.ofDual j)
          naturality := by
            intro j k h
            let J : JIndex := OrderDual.ofDual j
            let L : JIndex := OrderDual.ofDual k
            have hLJ : L.1 ≤ J.1 := leOfHom h
            change (BigAffineFppf.inclusion B S hS ⋙ Sheaf.sheafifiedYoneda Jsite).map
              (D.transition hLJ) ≫ xMap L = xMap J
            apply (cancel_mono f).1
            rw [Category.assoc, hmapFactor L, hmapFactor J]
            exact congrArg (fun q ↦ q ≫ p) (colimit.w (formalSpectrumDiagram D) h) } }
  refine ⟨colimit.desc (formalSpectrumDiagram D) c, colimit.hom_ext fun j ↦ ?_⟩
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q ↦ q ≫ f) (colimit.ι_desc c j)).trans (hmapFactor (OrderDual.ofDual j)))

/-- **Stacks 0AR0.** Let `f : X ⟶ Y` be a morphism of formal algebraic
spaces over `S` with `X` and `Y` locally Noetherian, `f` locally of finite type and `f` a
monomorphism. Then `f` is rig-surjective if and only if every adic morphism `Spf R ⟶ Y`, with
`R` a complete discrete valuation ring, factors through `X`.

The forward implication uses that `X` and `Y` are fpqc sheaves, Stacks 0AQD,
`AlgebraicGeometry.FormalSpace.isSheaf_fpqc`. -/
@[stacks 0AR0]
theorem isRigSurjective_iff_factorsAdicCompleteDvrPoints {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y)
    (hft : IsLocallyOfFiniteType B S hS f) [Mono f] :
    IsRigSurjective B S hS f ↔ FactorsAdicCompleteDvrPoints B S hS f :=
  ⟨factorsAdicCompleteDvrPoints_of_isRigSurjective B S hS f hX hY hft,
    isRigSurjective_of_factorsAdicCompleteDvrPoints B S hS f⟩

end AlgebraicGeometry.FormalSpace

end
