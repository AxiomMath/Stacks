module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationCokernel
public import StacksFrontier.Algebra.Homology.StupidTruncation
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.FiniteFreeComplex
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.UniformExtVanishingLocallyFree
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Restriction
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeTFAE
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.RestrictHomology
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.BoundedFlatRepresentative
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FlatCokernel
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FlatOpcycles
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.LocalTorAmplitude
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extending a perfect complex from a quasi-compact open after adding a shifted vector bundle

Let `X` be an affine scheme and `U ⊆ X` a quasi-compact open. Every perfect object `E` of
`D(𝒪_U)` becomes the restriction of a perfect object of `D(𝒪_X)` after a shifted finite locally
free sheaf is added to it: there are an integer `r` and a finite locally free `𝒪_U`-module `ℱ`
with `ℱ[-r] ⊕ E ≅ P|_U` for a perfect complex `P` on `X`. This is [Stacks, Tag 08EG].

## Main results

* `Stacks.DerivedQCoh.OpenLift.exists_finiteLocallyFree_biprod_iso_restrict_of_isPerfect` is the
  tag. The shifted summand is `(DerivedCategory.singleFunctor _ r).obj ℱ`, the sheaf `ℱ` placed
  in cohomological degree `r`, and the conclusion is an isomorphism with the image under the
  localization functor of the degreewise restriction of `P`, so the direct-sum shape is pinned.

## Implementation notes

**The proof.** By [Stacks, Tag 08CQ] the perfect object `E` is pseudo-coherent and locally of
finite Tor dimension, so [Stacks, Tag 08EE] writes it as the restriction to `U` of a bounded
above complex `𝒢` of finite free `𝒪_X`-modules. Quasi-compactness of `U` turns the per-member
Tor-amplitude intervals into a single interval `[a₀, b₀]` valid on all of `U`, and the cut `r`
is chosen at `a₀ - n₀`, where `n₀` is the degree beyond which `Ext` between finite locally free
`𝒪_U`-modules vanishes. Over `U` the cokernel `ℱ` of `𝒢^{r-2} → 𝒢^{r-1}` is then flat by
[Stacks, Tag 08CH], and flat plus finitely presented is finite locally free by
[Stacks, Tag 05P2]. The complex `𝒢|_U` is concentrated in degrees `≥ r - 1` by
[Stacks, Tag 08CI], so its truncation `L = τ_{≥r-1}(𝒢|_U)` still represents `E` and has `ℱ` in
its bottom degree. The short exact sequence `L^{r-1}[-(r-1)] ⟶ L ⟶ σ_{≥r}L` of stupid
truncations gives a distinguished triangle whose connecting morphism `L ⟶ L^{r-1}[-(r-1)]` is
zero; a distinguished triangle with vanishing third morphism is a biproduct, whence
`ℱ[-r] ⊕ E ≅ σ_{≥r}(𝒢|_U)`. Finally `σ_{≥r}𝒢` is a perfect complex on `X`, being bounded on
both sides with finite free terms, and its restriction to `U` is `σ_{≥r}(𝒢|_U)` because stupid
truncation commutes with the exact restriction functor and `τ_{≥r-1}` changes nothing in degrees
`≥ r`.

**Why the connecting morphism vanishes.** The source cites part (1) of [Stacks, Tag 09M4], a
window of degrees outside which a quasi-coherent object admits no nonzero morphism from a
perfect object; this library proves that only relative to a derived dual complex, which it does
not have. The vanishing needed here is obtained instead with no dual at all. The same
Tor-amplitude interval that makes `ℱ` finite locally free makes `τ_{≥a₀-1}(𝒢|_U)` a *bounded*
complex of finite locally free `𝒪_U`-modules representing `E`, concentrated in degrees
`[a₀ - 1, b_𝒢]`: its bottom term is the cokernel of `𝒢^{a₀-2} → 𝒢^{a₀-1}`, finite locally free
by the same two tags, and above the cut its terms are those of `𝒢|_U`. Induction on the stupid
truncations of that representative
(`Stacks.DerivedQCoh.subsingleton_hom_Q_obj_of_singleFunctor`) reduces the morphism group
`Hom(E, ℱ[-(r-1)])` to the groups `Ext^{i-(r-1)}(ℰ, ℱ)` between finite locally free modules,
with `i ≥ a₀ - 1`, so with `i - (r - 1) ≥ n₀`; and those vanish by
`Stacks.DerivedQCoh.exists_subsingleton_hom_singleFunctor_of_isCompact`, the bound of
[Stacks, Tag 08EF] made uniform in the target as well as the source. The cut `r = a₀ - n₀` is
exactly what buys the `n₀` degrees of separation.

**Why the derived category is the standard one.** [Stacks, Tag 08EE] is stated at an arbitrary
localization universe, but the splitting argument needs the t-structure and the single functors
of `CategoryTheory.HasDerivedCategory.standard`, and the choice of localization universe is not
mathematical content: the derived category is determined up to equivalence. The instance is
seated locally at a raised priority because the import closure carries the locally small
instances for sheaf categories as global ones.

## References

* [Stacks Project, Tag 08EG](https://stacks.math.columbia.edu/tag/08EG)
* [Stacks Project, Tag 08EE](https://stacks.math.columbia.edu/tag/08EE)
* [Stacks Project, Tag 08CQ](https://stacks.math.columbia.edu/tag/08CQ)
* [Stacks Project, Tag 08CH](https://stacks.math.columbia.edu/tag/08CH)
* [Stacks Project, Tag 08CI](https://stacks.math.columbia.edu/tag/08CI)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
* [Stacks Project, Tag 08EF](https://stacks.math.columbia.edu/tag/08EF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace StrictlyPerfect HomologicalComplex StacksDraft.StupidTruncation
open Stacks.Cohomology.PerfectComplexes Stacks.Cohomology.TorAmplitude

universe u

namespace Stacks.DerivedQCoh.OpenLift

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Stupid truncation and biproduct splittings -/

section Abstract

variable {C : Type*} [Category* C] [Abelian C]

/-- A complex concentrated in degrees `≥ n` is its own stupid truncation at `n`. -/
private lemma isIso_ιStupidTrunc (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyGE n] :
    IsIso (ιStupidTrunc K (ComplexShape.embeddingUpIntGE n)) := by
  suffices h : ∀ i, IsIso ((ιStupidTrunc K (ComplexShape.embeddingUpIntGE n)).f i) by
    let _ := h
    exact HomologicalComplex.Hom.isIso_of_components _
  intro i
  by_cases hi : n ≤ i
  · rw [ιStupidTruncGE_f K n i hi]
    infer_instance
  · exact IsZero.isIso
      (CochainComplex.isZero_of_isStrictlyGE _ n i (by omega))
      (CochainComplex.isZero_of_isStrictlyGE K n i (by omega)) _

/-- **The stupid truncation one step up splits off the bottom term.** For `K` concentrated in
degrees `≥ n`, the short exact sequence `K^n[-n] ⟶ K ⟶ σ_{≥n+1}K` rotates to a distinguished
triangle whose third morphism is the composite of `K ≅ σ_{≥n}K` with the projection to
`K^n[-n]`; it vanishes when there is no nonzero morphism `K ⟶ K^n[-n]` at all, and a
distinguished triangle with vanishing third morphism is a biproduct. -/
private lemma nonempty_biprod_iso_stupidTrunc [HasDerivedCategory.{u} C]
    (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyGE n]
    [Subsingleton (DerivedCategory.Q.obj K ⟶
      (DerivedCategory.singleFunctor C n).obj (K.X n))] :
    Nonempty (((DerivedCategory.singleFunctor C (n + 1)).obj (K.X n) ⊞
      DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj (K.stupidTrunc (ComplexShape.embeddingUpIntGE (n + 1)))) := by
  let _ := isIso_ιStupidTrunc K n
  let eK := DerivedCategory.Q.mapIso (asIso (ιStupidTrunc K (ComplexShape.embeddingUpIntGE n)))
  let T := DerivedCategory.triangleOfSES (stupidTruncGEShortComplex_shortExact K n)
  have hz : T.mor₂ = 0 := by
    change DerivedCategory.Q.map (stupidTruncGEπ K n) = 0
    have h : eK.inv ≫ DerivedCategory.Q.map (stupidTruncGEπ K n) = 0 := by
      change (eK.inv ≫ DerivedCategory.Q.map (stupidTruncGEπ K n) :
        DerivedCategory.Q.obj K ⟶ (DerivedCategory.singleFunctor C n).obj (K.X n)) = 0
      exact Subsingleton.elim _ _
    simpa using congrArg (fun f => eK.hom ≫ f) h
  have hz' : T.invRotate.mor₃ = 0 := by
    dsimp only [Triangle.invRotate]
    rw [hz]
    exact zero_comp
  obtain ⟨e, -, -⟩ := exists_iso_binaryBiproduct_of_distTriang T.invRotate
    (inv_rot_of_distTriang T (DerivedCategory.triangleOfSES_distinguished _)) hz'
  let es := ((DerivedCategory.singleFunctors C).shiftIso (-1) (n + 1) n (by omega)).app (K.X n)
  exact ⟨(biprod.mapIso es.symm eK.symm) ≪≫ e.symm⟩

/-- The canonical morphism to the truncation `τ_{≥n}K` is an isomorphism in every degree above
`n`, where neither complex is modified. -/
private lemma isIso_πTruncGE_f (K : CochainComplex C ℤ) (n i : ℤ) (hi : n < i) :
    IsIso ((K.πTruncGE n).f i) := by
  let e := ComplexShape.embeddingUpIntGE n
  have he : e.f (i - n).toNat = i := by change n + ((i - n).toNat : ℤ) = i; omega
  have hn : ¬ e.BoundaryGE (i - n).toNat := by
    change ¬ (ComplexShape.embeddingUpIntGE n).BoundaryGE (i - n).toNat
    rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff]
    omega
  change IsIso ((HomologicalComplex.πTruncGE K e).f i)
  dsimp only [HomologicalComplex.πTruncGE]
  rw [e.liftExtend_f _ _ he]
  let _ := K.isIso_restrictionToTruncGE' e (i - n).toNat hn
  exact ((K.restrictionXIso e he).symm ≪≫
    asIso ((K.restrictionToTruncGE' e).f (i - n).toNat) ≪≫
    ((K.truncGE' e).extendXIso e he).symm).isIso_hom

/-- A morphism of complexes which is an isomorphism in every degree `≥ n` induces an isomorphism
of the stupid truncations at `n`, which only see those degrees. -/
private lemma isIso_stupidTruncMap (K L : CochainComplex C ℤ) (f : K ⟶ L) (n : ℤ)
    (hf : ∀ i : ℤ, n ≤ i → IsIso (f.f i)) :
    IsIso (HomologicalComplex.stupidTruncMap f (ComplexShape.embeddingUpIntGE n)) := by
  let e := ComplexShape.embeddingUpIntGE n
  suffices h : ∀ i, IsIso ((HomologicalComplex.stupidTruncMap f e).f i) by
    let _ := h
    exact HomologicalComplex.Hom.isIso_of_components _
  intro i
  by_cases hi : n ≤ i
  · have he : e.f (i - n).toNat = i := by change n + ((i - n).toNat : ℤ) = i; omega
    let _ := hf i hi
    have h : IsIso ((HomologicalComplex.stupidTruncMap f e).f i ≫
        (L.stupidTruncXIso e he).hom) := by
      rw [HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (L.stupidTruncXIso e he).hom
  · exact IsZero.isIso
      (CochainComplex.isZero_of_isStrictlyGE _ n i (by omega))
      (CochainComplex.isZero_of_isStrictlyGE _ n i (by omega)) _

/-- An additive functor commutes with stupid truncation from below: both complexes are the
original one in degrees `≥ n` and zero below. -/
private lemma nonempty_map_stupidTrunc_iso {D : Type*} [Category* D] [Abelian D] (F : C ⥤ D)
    [F.Additive] (K : CochainComplex C ℤ) (n : ℤ) :
    Nonempty ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (K.stupidTrunc (ComplexShape.embeddingUpIntGE n)) ≅
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).stupidTrunc
        (ComplexShape.embeddingUpIntGE n)) := by
  let e := ComplexShape.embeddingUpIntGE n
  let P := K.stupidTrunc e
  let M := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let f := M.map (ιStupidTrunc K e)
  let _ : CochainComplex.IsStrictlyGE (M.obj P) n := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact F.map_isZero (CochainComplex.isZero_of_isStrictlyGE P n i hi)
  let g := liftStupidTrunc (M.obj K) e f
  have hcomp : g ≫ ιStupidTrunc (M.obj K) e = f := liftStupidTrunc_ι _ _ _
  have h (i : ℤ) : IsIso (g.f i) := by
    by_cases hi : n ≤ i
    · have hfi : IsIso (f.f i) := by
        change IsIso (F.map ((ιStupidTrunc K e).f i))
        rw [ιStupidTruncGE_f K n i hi]
        infer_instance
      have hg : IsIso (g.f i ≫ (ιStupidTrunc (M.obj K) e).f i) := by
        rw [← HomologicalComplex.comp_f, hcomp]
        exact hfi
      have hι : IsIso ((ιStupidTrunc (M.obj K) e).f i) := by
        rw [ιStupidTruncGE_f (M.obj K) n i hi]
        infer_instance
      exact IsIso.of_isIso_comp_right _ ((ιStupidTrunc (M.obj K) e).f i)
    · exact IsZero.isIso
        (CochainComplex.isZero_of_isStrictlyGE _ n i (by omega))
        (CochainComplex.isZero_of_isStrictlyGE _ n i (by omega)) _
  let _ := h
  let _ := HomologicalComplex.Hom.isIso_of_components g
  exact ⟨asIso g⟩

end Abstract

/-! ### Sheaves locally isomorphic to finite free sheaves -/

/-- A free sheaf of modules on a finite index type is finite locally free: its canonical global
basis is already a local free basis with a finite index type. -/
private theorem isFiniteLocallyFree_free (X : Scheme.{u}) (I : Type u) [Finite I] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (SheafOfModules.free (R := X.ringCatSheaf) I) := by
  let q := (SheafOfModules.free.generatingSections (R := X.ringCatSheaf) I).localGeneratorsData
  refine AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.mk.{u, u, u} ⟨q, inferInstance, ?_⟩
  constructor
  intro i
  exact ⟨inferInstanceAs (Finite I)⟩

/-- A finite locally free sheaf of modules is quasi-coherent, with the hypothesis taken as an
argument rather than an instance. -/
private theorem isQuasicoherent_of_isFiniteLocallyFree {X : Scheme.{u}} (M : X.Modules)
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) :
    M.IsQuasicoherent :=
  have := h
  Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree M

/-- **Flat and finitely presented implies finite locally free**, the implication (1) ⟹ (4) of
[Stacks, Tag 05P2]; a finitely presented sheaf of modules is quasi-coherent, which is the
standing hypothesis of the five-way equivalence. -/
@[ega "IV 2.1.12" "(a) ⇒ (b), special case"]
private theorem isFiniteLocallyFree_of_isFlat {X : Scheme.{u}} (M : X.Modules)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) M)
    (hfp : M.IsFinitePresentation) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M := by
  have := hfp
  have hqc : M.IsQuasicoherent := by
    constructor
    exact ⟨(SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose⟩
  have := hqc
  have hconj : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) M ∧
    M.IsFinitePresentation := ⟨hflat, hfp⟩
  exact ((Stacks.FiniteLocallyFree.ModuleTFAE.finiteLocallyFree_tfae M).out 1 4).mp hconj

/-- A sheaf of modules isomorphic to a free sheaf on a finite index type is finite locally
free. -/
private theorem isFiniteLocallyFree_of_iso_free {X : Scheme.{u}} (M : X.Modules)
    (h : ∃ I : Type u, Finite I ∧ Nonempty (M ≅ SheafOfModules.free (R := X.ringCatSheaf) I)) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M := by
  obtain ⟨I, hI, ⟨e⟩⟩ := h
  have := hI
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso e.symm
    (h := isFiniteLocallyFree_free X I)

/-- A zero sheaf of modules on a scheme is quasi-coherent, being free on an empty index type. -/
private theorem isQuasicoherent_of_isZero {X : Scheme.{u}} (M : X.Modules) (hM : IsZero M) :
    M.IsQuasicoherent := by
  have hZ : IsZero (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} Empty)) := by
    refine (IsZero.iff_id_eq_zero _).mpr ?_
    refine (SheafOfModules.freeHomEquiv _).injective ?_
    funext i
    exact i.down.elim
  exact isQuasicoherent_of_isFiniteLocallyFree M
    (isFiniteLocallyFree_of_iso_free M ⟨ULift.{u} Empty, inferInstance, ⟨(hZ.iso hM).symm⟩⟩)

/-- A sheaf of modules isomorphic to a free sheaf on a finite index type is flat and of finite
presentation. This is the implication (4) ⟹ (1) of [Stacks, Tag 05P2]. -/
private theorem isFlat_and_isFinitePresentation_of_iso_free {X : Scheme.{u}} (M : X.Modules)
    (h : ∃ I : Type u, Finite I ∧ Nonempty (M ≅ SheafOfModules.free (R := X.ringCatSheaf) I)) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) M ∧
      M.IsFinitePresentation := by
  have hM := isFiniteLocallyFree_of_iso_free M h
  have : M.IsQuasicoherent := isQuasicoherent_of_isFiniteLocallyFree M hM
  exact ((Stacks.FiniteLocallyFree.ModuleTFAE.finiteLocallyFree_tfae M).out 4 1).mp hM

/-- A sheaf of modules isomorphic to a free sheaf on a finite index type is a direct summand of
a finite free sheaf, in the sense of [Stacks, Tag 08C4]: reindexing by `Fin n` turns the free
sheaf into `𝒪_X^{⊕n}`. -/
private theorem isDirectSummandOfFiniteFree_of_iso_free {X : Scheme.{u}} (M : X.Modules)
    (h : ∃ I : Type u, Finite I ∧ Nonempty (M ≅ SheafOfModules.free (R := X.ringCatSheaf) I)) :
    IsDirectSummandOfFiniteFree (X := X.toRingedSpace) M := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := h
  have := hI
  let _ := Fintype.ofFinite I
  refine (isDirectSummandOfFiniteFree_iff_retract M).mpr ?_
  let e' : SheafOfModules.free (R := X.ringCatSheaf) I ≅
      finiteFree X.toRingedSpace (Fintype.card I) :=
    Sigma.reindex (Fintype.equivFin I) (fun _ => SheafOfModules.unit X.ringCatSheaf) ≪≫
      (biproduct.isoCoproduct (fun _ : Fin (Fintype.card I) =>
        structureModule X.toRingedSpace)).symm
  exact ⟨Fintype.card I, ⟨(e ≪≫ e').retract⟩⟩

/-- A zero sheaf of modules is a direct summand of the finite free sheaf of rank zero. -/
private theorem isDirectSummandOfFiniteFree_of_isZero {X : RingedSpace.{u, u}}
    (M : OXMod.{u, u, u} X) (h : IsZero M) : IsDirectSummandOfFiniteFree M :=
  (isDirectSummandOfFiniteFree_iff_retract M).mpr
    ⟨0, ⟨{ i := 0, r := 0, retract := h.eq_of_src _ _ }⟩⟩

/-- Restriction to an open subscheme carries a sheaf isomorphic to a free sheaf on a finite
index type to one isomorphic to the free sheaf on the same index type. -/
private theorem iso_free_restrict {X : Scheme.{u}} (V : X.Opens) (M : X.Modules)
    (h : ∃ I : Type u, Finite I ∧ Nonempty (M ≅ SheafOfModules.free (R := X.ringCatSheaf) I)) :
    ∃ I : Type u, Finite I ∧ Nonempty
      ((AlgebraicGeometry.RingedSpace.restrictModules.{u, u} X.toRingedSpace V).obj M ≅
        SheafOfModules.free (R := V.toScheme.ringCatSheaf) I) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := h
  refine ⟨I, hI, ⟨?_⟩⟩
  exact (Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict X V).app M ≪≫
    (Scheme.Modules.restrictFunctor V.ι).mapIso e ≪≫
    (Scheme.Modules.restrictFreeIso V.ι I).symm

/-! ### The two global inputs extracted from the local data -/

/-- **The stupid truncation of a bounded above complex of finite free modules is perfect.** It is
bounded on both sides and each of its terms is a direct summand of a finite free module, so the
one-member covering of `X` by itself already exhibits it as strictly perfect. -/
private theorem isPerfectComplex_stupidTrunc (X : Scheme.{u}) (G : CochainComplex X.Modules ℤ)
    (r b : ℤ) (hb : ∀ i : ℤ, b < i → IsZero (G.X i))
    (hf : ∀ i : ℤ, ∃ I : Type u, Finite I ∧
      Nonempty (G.X i ≅ SheafOfModules.free (R := X.ringCatSheaf) I)) :
    IsPerfectComplex (G.stupidTrunc (ComplexShape.embeddingUpIntGE r)) := by
  let P := G.stupidTrunc (ComplexShape.embeddingUpIntGE r)
  let R := AlgebraicGeometry.RingedSpace.restrictModules.{u, u} X.toRingedSpace ⊤
  let PT := (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have hid : QuasiIso (𝟙 PT) := quasiIso_of_isIso _
  refine ⟨PUnit.{u + 1}, fun _ => ⊤, by simp, fun _ => ⟨PT, ⟨?_, ?_⟩, 𝟙 PT, hid⟩⟩
  · refine (Set.finite_Icc r b).subset fun i hi => ?_
    by_contra h
    simp only [Set.mem_Icc, not_and_or, not_le] at h
    refine hi (R.map_isZero ?_)
    rcases h with h | h
    · exact CochainComplex.isZero_of_isStrictlyGE P r i h
    · by_cases hr : r ≤ i
      · exact (hb i h).of_iso (stupidTruncGEXIso G r i hr)
      · exact CochainComplex.isZero_of_isStrictlyGE P r i (by omega)
  · intro i
    by_cases hi : r ≤ i
    · refine isDirectSummandOfFiniteFree_of_iso_free (X := (⊤ : X.Opens).toScheme) _ ?_
      obtain ⟨I, hI, ⟨e⟩⟩ := iso_free_restrict (⊤ : X.Opens) (G.X i) (hf i)
      exact ⟨I, hI, ⟨R.mapIso (stupidTruncGEXIso G r i hi) ≪≫ e⟩⟩
    · exact isDirectSummandOfFiniteFree_of_isZero _
        (R.map_isZero (CochainComplex.isZero_of_isStrictlyGE P r i (by omega)))

/-- **On a quasi-compact scheme, locally finite Tor dimension gives one global interval.** The
covering witnessing local finiteness has a finite subcover, over which the finitely many
intervals are contained in a single one; Tor amplitude in a fixed interval is local on a
covering, so that interval works on the whole space. -/
private theorem exists_hasTorAmplitude_of_locallyHasFiniteTorDimension (Y : Scheme.{u})
    [CompactSpace Y.carrier] (E : DerivedCategory Y.Modules)
    (h : LocallyHasFiniteTorDimension Y.toRingedSpace E) :
    ∃ a b : ℤ, HasTorAmplitude Y.toRingedSpace E a b := by
  classical
  obtain ⟨J, W, hW, hTor⟩ := h
  choose a b hAmp using hTor
  obtain ⟨s, hs⟩ := (isCompact_univ : IsCompact (Set.univ : Set Y.carrier)).elim_finite_subcover
    (fun j => (W j : Set Y.carrier)) (fun j => (W j).isOpen) (by
      intro x _
      obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (show x ∈ iSup W by rw [hW]; trivial)
      exact Set.mem_iUnion.2 ⟨j, hj⟩)
  obtain ⟨a₀, ha₀⟩ := Finite.bddBelow_range (fun j : {j // j ∈ s} => a j.1)
  obtain ⟨b₀, hb₀⟩ := Finite.bddAbove_range (fun j : {j // j ∈ s} => b j.1)
  refine ⟨a₀, b₀, hasTorAmplitude_of_iSup_eq_top Y.toRingedSpace E a₀ b₀
    (fun j : {j // j ∈ s} => W j.1) ?_ fun j => ?_⟩
  · refine top_unique fun x _ => Opens.mem_iSup.mpr ?_
    obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact ⟨⟨j, hj⟩, hx⟩
  · exact FlatOpcycles.hasTorAmplitude_mono.{u, u + 1}
      (X := Y.toRingedSpace.restrict (W j.1).isOpenEmbedding)
      (hAmp j.1) (ha₀ ⟨j, rfl⟩) (hb₀ ⟨j, rfl⟩)

/-- **The bottom cokernel of a complex of finite free modules of Tor amplitude in `[a, b]` is
finite locally free.** The complex is bounded above with flat terms, so the cokernel of its
differential into degree `a` is flat by [Stacks, Tag 08CH]; it is finitely presented because it
is a cokernel of a map between finitely presented modules, hence quasi-coherent, and flat plus
finitely presented is finite locally free by [Stacks, Tag 05P2]. -/
private theorem isFiniteLocallyFree_cokernel (Y : Scheme.{u}) (K : CochainComplex Y.Modules ℤ)
    (a b n : ℤ) (hn : ∀ i : ℤ, n < i → IsZero (K.X i))
    (hfree : ∀ i : ℤ, ∃ I : Type u, Finite I ∧
      Nonempty (K.X i ≅ SheafOfModules.free (R := Y.ringCatSheaf) I))
    (hamp : HasTorAmplitude Y.toRingedSpace (DerivedCategory.Q.obj K) a b) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (cokernel (K.d (a - 1) a)) := by
  have hbound : CochainComplex.IsStrictlyLE K n := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => hn i hi
  have hflat := FlatCokernel.isFlat_cokernel_of_hasTorAmplitude (X := Y.toRingedSpace) K a b
    ⟨n, hbound⟩ (fun i => (isFlat_and_isFinitePresentation_of_iso_free (K.X i) (hfree i)).1) hamp
  have hfp : (cokernel (K.d (a - 1) a)).IsFinitePresentation := by
    have := (isFlat_and_isFinitePresentation_of_iso_free (K.X a) (hfree a)).2
    have := isFiniteLocallyFree_of_iso_free (K.X (a - 1)) (hfree (a - 1))
    have := Stacks.AlgebraicGeometry.CoherenceCriteria.isFiniteType_of_isFiniteLocallyFree
      (K.X (a - 1))
    exact Stacks.SheafOfModules.isFinitePresentation_cokernel (K.d (a - 1) a)
  exact isFiniteLocallyFree_of_isFlat _ hflat hfp

/-! ### Stacks 08EG -/

/-- **[Stacks, Tag 08EG].** Let `X` be an affine scheme and `U ⊆ X` a quasi-compact open. For
every perfect object `E` of `D(𝒪_U)` there are an integer `r`, a finite locally free
`𝒪_U`-module `ℱ` and a perfect complex `P` of `𝒪_X`-modules with `ℱ[-r] ⊕ E ≅ P|_U`, where
`ℱ[-r]` is `ℱ` placed in cohomological degree `r`. -/
@[stacks 08EG]
theorem exists_finiteLocallyFree_biprod_iso_restrict_of_isPerfect
    (X : Scheme.{u}) [IsAffine X] (U : X.Opens) (hU : IsCompact (U : Set X))
    (E : DerivedCategory U.toScheme.Modules)
    (hE : IsPerfect (X := U.toScheme.toRingedSpace) E) :
    ∃ (r : ℤ) (F : U.toScheme.Modules) (P : CochainComplex (OXMod.{u, u, u} X.toRingedSpace) ℤ),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F ∧
      IsPerfectComplex P ∧
      Nonempty (((DerivedCategory.singleFunctor U.toScheme.Modules r).obj F ⊞ E) ≅
        DerivedCategory.Q.obj
          (((AlgebraicGeometry.RingedSpace.restrictModules.{u, u} X.toRingedSpace
            U).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) := by
  classical
  have hcomp : CompactSpace U.toScheme.carrier := isCompact_iff_compactSpace.mp hU
  -- The degree beyond which `Ext` between finite locally free `𝒪_U`-modules vanishes.
  obtain ⟨n₀, hn₀, hExt⟩ := exists_subsingleton_hom_singleFunctor_of_isCompact (X := X) U hU
  -- Tag 08CQ: `E` is pseudo-coherent and locally of finite Tor dimension.
  obtain ⟨hpc, htor⟩ := (isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension
    (X := U.toScheme.toRingedSpace) E).mp hE
  -- Tag 08EE: `E` is the restriction of a bounded above complex of finite free modules on `X`.
  obtain ⟨G, ⟨bG, hbG⟩, hGfree, ⟨eG⟩⟩ := AlgebraicGeometry.exists_boundedAbove_finiteFree_lift
    X U hU E ((isPseudoCoherent_iff_isPseudoCoherent' E).mp hpc)
  -- Quasi-compactness of `U` turns the local Tor-amplitude intervals into one global interval.
  obtain ⟨a₀, b₀, hampE⟩ :=
    exists_hasTorAmplitude_of_locallyHasFiniteTorDimension U.toScheme E htor
  -- Place the cut `n₀` below the bottom of the Tor-amplitude interval.
  let r : ℤ := a₀ - n₀
  have hrdef : r = a₀ - n₀ := rfl
  have hra : r ≤ a₀ - 1 := by omega
  have hamp : HasTorAmplitude U.toScheme.toRingedSpace E (r - 1) (max b₀ r) :=
    FlatOpcycles.hasTorAmplitude_mono.{u, u + 1} hampE (by omega) (le_max_left _ _)
  -- The restriction of the finite free complex to `U`, and its properties.
  let RU := AlgebraicGeometry.RingedSpace.restrictModules.{u, u} X.toRingedSpace U
  let GY : CochainComplex U.toScheme.Modules ℤ :=
    (RU.mapHomologicalComplex (ComplexShape.up ℤ)).obj G
  have eGY : DerivedCategory.Q.obj GY ≅ E := eG
  have hGYfree (i : ℤ) : ∃ I : Type u, Finite I ∧
      Nonempty (GY.X i ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) I) :=
    iso_free_restrict U (G.X i) (hGfree i)
  have hGYbound (i : ℤ) (hi : bG < i) : IsZero (GY.X i) := RU.map_isZero (hbG i hi)
  have hampGY : HasTorAmplitude U.toScheme.toRingedSpace (DerivedCategory.Q.obj GY)
      (r - 1) (max b₀ r) := FlatOpcycles.hasTorAmplitude_of_iso.{u, u + 1} hamp eGY
  -- Tags 08CH and 05P2: the cokernel of the differential into degree `r - 1` is finite locally
  -- free.
  have hFLF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (cokernel (GY.d (r - 2) (r - 1))) := by
    have h := isFiniteLocallyFree_cokernel U.toScheme GY (r - 1) (max b₀ r) bG hGYbound
      hGYfree hampGY
    rwa [show r - 1 - 1 = r - 2 by omega] at h
  -- Tag 08CI: `E` is concentrated in degrees `≥ r - 1`, hence so is the restricted complex.
  have hEGE : E.IsGE (r - 1) := by
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact BoundedFlatRepresentative.isZero_homology_of_hasTorAmplitude
      (X := U.toScheme.toRingedSpace) E (r - 1) (max b₀ r) hamp i
      (by simp only [Set.mem_Icc]; omega)
  have hGYGE : GY.IsGE (r - 1) :=
    (DerivedCategory.isGE_Q_obj_iff GY (r - 1)).mp
      (DerivedCategory.TStructure.t.isGE_of_iso eGY.symm (r - 1))
  -- The truncation at `r - 1` still represents `E` and has the cokernel in its bottom degree.
  let L := GY.truncGE (r - 1)
  let eL : DerivedCategory.Q.obj L ≅ E :=
    (asIso (DerivedCategory.Q.map (GY.πTruncGE (r - 1)))).symm ≪≫ eGY
  let eF : L.X (r - 1) ≅ cokernel (GY.d (r - 2) (r - 1)) :=
    GY.truncGEXIsoOpcycles (r - 1) ≪≫
      (GY.opcyclesIsCokernel (r - 2) (r - 1) (by
        apply (ComplexShape.up ℤ).prev_eq'
        change r - 2 + 1 = r - 1
        omega)).coconePointUniqueUpToIso (colimit.isColimit _)
  have hFL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (L.X (r - 1)) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso eF.symm (h := hFLF)
  -- The same construction at the cut `a₀ - 1` gives a *bounded* finite locally free
  -- representative of `E`, concentrated in degrees `[a₀ - 1, bG]`.
  have hamp₀ : HasTorAmplitude U.toScheme.toRingedSpace E (a₀ - 1) (max b₀ (a₀ - 1)) :=
    FlatOpcycles.hasTorAmplitude_mono.{u, u + 1} hampE (by omega) (le_max_left _ _)
  have hampGY₀ : HasTorAmplitude U.toScheme.toRingedSpace (DerivedCategory.Q.obj GY)
      (a₀ - 1) (max b₀ (a₀ - 1)) := FlatOpcycles.hasTorAmplitude_of_iso.{u, u + 1} hamp₀ eGY
  have hFLF₀ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (cokernel (GY.d (a₀ - 2) (a₀ - 1))) := by
    have h := isFiniteLocallyFree_cokernel U.toScheme GY (a₀ - 1) (max b₀ (a₀ - 1)) bG hGYbound
      hGYfree hampGY₀
    rwa [show a₀ - 1 - 1 = a₀ - 2 by omega] at h
  have hEGE₀ : E.IsGE (a₀ - 1) := by
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact BoundedFlatRepresentative.isZero_homology_of_hasTorAmplitude
      (X := U.toScheme.toRingedSpace) E (a₀ - 1) (max b₀ (a₀ - 1)) hamp₀ i
      (by simp only [Set.mem_Icc]; omega)
  have hGYGE₀ : GY.IsGE (a₀ - 1) :=
    (DerivedCategory.isGE_Q_obj_iff GY (a₀ - 1)).mp
      (DerivedCategory.TStructure.t.isGE_of_iso eGY.symm (a₀ - 1))
  let L₀ := GY.truncGE (a₀ - 1)
  let eL₀ : DerivedCategory.Q.obj L₀ ≅ E :=
    (asIso (DerivedCategory.Q.map (GY.πTruncGE (a₀ - 1)))).symm ≪≫ eGY
  let eF₀ : L₀.X (a₀ - 1) ≅ cokernel (GY.d (a₀ - 2) (a₀ - 1)) :=
    GY.truncGEXIsoOpcycles (a₀ - 1) ≪≫
      (GY.opcyclesIsCokernel (a₀ - 2) (a₀ - 1) (by
        apply (ComplexShape.up ℤ).prev_eq'
        change a₀ - 2 + 1 = a₀ - 1
        omega)).coconePointUniqueUpToIso (colimit.isColimit _)
  have hL₀zeroLow (i : ℤ) (hi : i < a₀ - 1) : IsZero (L₀.X i) :=
    CochainComplex.isZero_of_isStrictlyGE _ (a₀ - 1) i hi
  have hL₀zeroHigh (i : ℤ) (hi : max bG (a₀ - 1) < i) : IsZero (L₀.X i) := by
    have := isIso_πTruncGE_f GY (a₀ - 1) i (by omega)
    exact (hGYbound i (by omega)).of_iso (asIso ((GY.πTruncGE (a₀ - 1)).f i)).symm
  have hL₀flf (i : ℤ) (hi : a₀ - 1 ≤ i) :
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (L₀.X i) := by
    by_cases hieq : i = a₀ - 1
    · subst hieq
      exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso eF₀.symm (h := hFLF₀)
    · have := isIso_πTruncGE_f GY (a₀ - 1) i (by omega)
      exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso
        (asIso ((GY.πTruncGE (a₀ - 1)).f i))
        (h := isFiniteLocallyFree_of_iso_free (GY.X i) (hGYfree i))
  have hL₀supp : {i : ℤ | ¬ IsZero (L₀.X i)}.Finite := by
    refine Set.Finite.subset (Set.finite_Icc (a₀ - 1) (max bG (a₀ - 1))) fun i hi => ?_
    simp only [Set.mem_Icc]
    refine ⟨?_, ?_⟩
    · by_contra hc
      exact hi (hL₀zeroLow i (by omega))
    · by_contra hc
      exact hi (hL₀zeroHigh i (by omega))
  -- The bottom term of `L` sits in degree `r - 1`, which is `n₀` below the bottom degree of the
  -- representative `L₀`, so every term of `L₀` has no nonzero morphism into it.
  have hS : Subsingleton (E ⟶ (DerivedCategory.singleFunctor U.toScheme.Modules (r - 1)).obj
      (L.X (r - 1))) := by
    refine subsingleton_hom_of_iso eL₀.symm (Iso.refl _) ?_
    refine subsingleton_hom_Q_obj_of_singleFunctor L₀ hL₀supp _ fun i => ?_
    by_cases hi : a₀ - 1 ≤ i
    · exact hExt (L₀.X i) (L.X (r - 1)) (hL₀flf i hi) hFL i (r - 1) (by omega)
    · exact subsingleton_hom_of_isZero_source
        ((DerivedCategory.singleFunctor U.toScheme.Modules i).map_isZero
          (hL₀zeroLow i (by omega)))
  have hsub : Subsingleton (DerivedCategory.Q.obj L ⟶
      (DerivedCategory.singleFunctor U.toScheme.Modules (r - 1)).obj (L.X (r - 1))) :=
    ⟨fun f g => by
      have h : eL.inv ≫ f = eL.inv ≫ g := hS.elim _ _
      simpa using congrArg (fun k => eL.hom ≫ k) h⟩
  -- The stupid truncation at `r` splits off that bottom term.
  have := hsub
  obtain ⟨eSplit⟩ := nonempty_biprod_iso_stupidTrunc L (r - 1)
  obtain ⟨eSplit'⟩ : Nonempty (((DerivedCategory.singleFunctor U.toScheme.Modules r).obj
      (L.X (r - 1)) ⊞ DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (L.stupidTrunc (ComplexShape.embeddingUpIntGE r))) := by
    simpa only [show r - 1 + 1 = r by omega] using Nonempty.intro eSplit
  -- The same stupid truncation of the complex on `X` is perfect and restricts to it.
  have := isIso_stupidTruncMap GY L (GY.πTruncGE (r - 1)) r
    fun i hi => isIso_πTruncGE_f GY (r - 1) i (by omega)
  obtain ⟨eRestrict⟩ := nonempty_map_stupidTrunc_iso RU G r
  refine ⟨r, cokernel (GY.d (r - 2) (r - 1)),
    G.stupidTrunc (ComplexShape.embeddingUpIntGE r), hFLF,
    isPerfectComplex_stupidTrunc X G r bG hbG hGfree, ⟨?_⟩⟩
  exact biprod.mapIso ((DerivedCategory.singleFunctor U.toScheme.Modules r).mapIso eF.symm)
      eL.symm ≪≫ eSplit' ≪≫
    (DerivedCategory.Q.mapIso (asIso (HomologicalComplex.stupidTruncMap (GY.πTruncGE (r - 1))
      (ComplexShape.embeddingUpIntGE r)))).symm ≪≫ (DerivedCategory.Q.mapIso eRestrict).symm

end Stacks.DerivedQCoh.OpenLift

end
