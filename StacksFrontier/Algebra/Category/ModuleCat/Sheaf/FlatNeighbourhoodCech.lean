module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatNeighbourhoodQuasiIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorUnitSmul
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AwayTensorBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ExtendedCechFunctoriality
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulCechColimit
public import StacksFrontier.Homology.HomologyColimit
public import Mathlib.Combinatorics.Pigeonhole
import StacksCore.Tactic.EgaSgaAttribute
import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedExistence

/-!
# Flat neighbourhood base change is a quasi-isomorphism on the extended alternating Čech complex

Let `φ : O ⟶ O'` be a flat morphism of sheaves of commutative rings on a site which is an
isomorphism modulo an ideal sheaf `I`, and let `f₁, …, f_r` be global sections of `O` generating
`I`.  This file proves [Stacks, Tag 099H]: extension of scalars along `φ`, applied degreewise, is
a quasi-isomorphism on the extended alternating Čech complex

`O → ∏_{i₀} O_{f_{i₀}} → ∏_{i₀ < i₁} O_{f_{i₀} f_{i₁}} → ⋯ → O_{f_1 ⋯ f_r}`.

The lower row of the source's square is identified with the extended alternating Čech complex of
the images of `f₁, …, f_r` in `O'`, so the comparison stated is the one the source displays; see
the note on the lower row below.

The argument is the source's.  The Čech complex is the colimit of the Koszul complexes
`K(O, f₁^{n+1}, …, f_r^{n+1})`; cohomology commutes with that colimit; and on each Koszul
approximant the comparison is invertible on cohomology because the Koszul cohomology sheaves are
annihilated by a power of `I`.

## Main results

* `Stacks.Sheaves.FlatNeighbourhood.prod_smul_eq_zero_of_exists_sections`: the pigeonhole step
  of the source's proof over one object — a module killed by a fixed power `N` of each of `r`
  sections is killed by the product of `r * N + 1` sections of the ideal they span there.
* `Stacks.Sheaves.FlatNeighbourhood.isAnnihilatedByPow_of_pow_smul_eq_zero`: the same conclusion
  from *local* generation of the ideal, which is what generation of a sheaf of ideals by global
  sections means — a module killed by a fixed power `N` of each of `r` generators of the ideal is
  annihilated by the power `r * N + 1` of the ideal.
* `Stacks.Sheaves.FlatNeighbourhood.exists_covering_sieve_le`: finitely many covering sieves on
  one object are refined by a single covering sieve.
* `Stacks.Sheaves.FlatNeighbourhood.isIso_app_of_isColimit`: a natural transformation invertible
  at every object of a diagram is invertible at a colimit of it that both functors preserve.
* `Stacks.Sheaves.CechFlatNeighbourhood.koszulComplex_powFamily_eq`: the Koszul complex of the
  family of `(n+1)`-st powers, as built from global sections in
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/KoszulGlobalSectionsAnnihilation.lean`, is the
  `n`-th Koszul power complex `AlgebraicGeometry.RingedSite.koszulPowerComplex` of the ringed-site
  development.
* `Stacks.Sheaves.CechFlatNeighbourhood.isAnnihilatedByPow_homology_koszulPowerComplex`: every
  cohomology sheaf of that Koszul power complex is annihilated by a power of `I`.
* `Stacks.Sheaves.CechFlatNeighbourhood.tensorExtendedAlternatingCechIso`: the lower row of the
  source's square — extension of scalars applied degreewise to `Č(f)` — is the extended
  alternating Čech complex of the system `S ↦ O_{f_S} ⊗_O O'`.
* `Stacks.Sheaves.CechFlatNeighbourhood.awayLocalizationBaseChangeIso`: **`O_{f_S} ⊗_O O'` is
  `O'_{f'_S}`, naturally in `S`** — that is, the base change of the system of localizations the
  Čech complex is built from is the system of localizations of `O'`.
* `Stacks.Sheaves.CechFlatNeighbourhood.extendedAlternatingCechBaseChangeIso`: consequently
  **the lower row is `Č(O')`**, the extended alternating Čech complex of the images of
  `f₁, …, f_r` in `O'`, read as a complex of `O`-modules; and
  `Stacks.Sheaves.CechFlatNeighbourhood.extendedAlternatingCechBaseChangeMap` is the comparison
  `Č(O) ⟶ Č(O')` of the source's square.
* `Stacks.Sheaves.CechFlatNeighbourhood.quasiIso_extendedAlternatingCechBaseChangeMap`:
  the comparison is a quasi-isomorphism — [Stacks, Tag 099H] in the general form its proof
  gives; the tag is registered on its consequence
  `Stacks.Sheaves.CechFlatNeighbourhood.quasiIso_complexMap_cechSystemBaseChangeMap` of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FlatNeighbourhoodCechNatural.lean`.

## Implementation notes

Two developments of the Koszul complex of a finite family of global sections of a sheaf of rings
meet here, and `koszulFunctor_powFamily_eq` identifies them.  Both are the alternating complex
`CategoryTheory.AlternatingCech.complex` of the system constant at the rank-one module whose
transition map along `S ⊆ T` is multiplication by a monomial in the sections; they differ only in
how that monomial is written, as `∏_{i ∈ T ∖ S} f_i^{n+1}` on one side and as
`∏_i f_i^{e_i}` with `e` the indicator of `T ∖ S` scaled by `n+1` on the other.  The two systems
are therefore *equal*, not merely isomorphic, and the identification is a `Functor.ext` whose
object clause is `rfl`.

The extended alternating Čech complex is built for a ringed site, while extension of scalars
along a morphism of sheaves of rings is built for a bare sheaf of commutative rings on a site;
`ringedSite` packages the latter data into the former.  Everything is stated in the second
language, because `AlgebraicGeometry.RingedSite.ringSheaf` is by definition
`Stacks.SheafOfModules.Tensor.ringSheaf` of the structure sheaf: carrying a
`RingedSite` as the variable instead leaves the sheaf-of-rings argument of
`Stacks.SheafOfModules.Tensor.ringSheaf` to be recovered from a projection, which instance search
cannot do.

Exactness of sequential colimits comes from [Stacks, Tag 03DB] at the module universe, lowered to
`Type 0` shapes by `CategoryTheory.AB5OfSize_of_univLE`; preservation of those colimits by the
tensor endofunctor is [Stacks, Tag 05NB], added as
`Stacks.SheafOfModules.FlatSheafification.sheafTensorRight_preservesColimits` (the finite case
already present there does not suffice).

## The lower row

The source's displayed square has the extended alternating Čech complex *of `O'`* as its lower
row, and observes without proof, inside the proof of the lemma, that it is the tensor product of
the upper row with `O'`.  That observation is proved here, so the statement below is of the
comparison `Č(O) ⟶ Č(O')` the source displays.  It comes in two halves.

**The lower row is a Čech complex of the right shape.**  Extension of scalars applied degreewise
to `Č(f)` is the extended alternating Čech complex of the system `S ↦ O_{f_S} ⊗_O O'`:
`tensorExtendedAlternatingCechIso`, one application of
`CategoryTheory.AlternatingCech.mapComplexIso`, whose two inputs — compatibility with the finite
products over `{S : Finset (Fin r) // S.card = p}` that form the terms, and commutation with the
alternating differential — are additivity of the tensor endofunctor and preservation of finite
products by it, the latter being the hypothesis, assumed below, that the functor
`(Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj (RestrictedRingModule φ)` preserves finite
limits.

**That system is the system of localizations of `O'`, naturally in `S`.**  This is
`awayLocalizationBaseChangeIso`, and it is proved through the Koszul approximants rather than by
comparing sheafifications.  The system `S ↦ O_{f_S}` is the colimit of the Koszul systems
`AlgebraicGeometry.RingedSite.koszulPowerFunctor`, which are *constant* at `O` and whose
transition maps are multiplications by monomials in the `f_i`; that is
`AlgebraicGeometry.RingedSite.isColimitKoszulPowerFunctorCocone`, the system-level half of
[Stacks, Tag 0913], and it holds over `O'` just as well.  On a constant system the comparison is
a single isomorphism `O ⊗_O O' ≅ O'`
(`AlgebraicGeometry.SheafOfModules.sheafTensorRightUnitIso`), and its naturality is one statement
about multiplication by a global section: the tensor endofunctor carries that multiplication to
that multiplication
(`AlgebraicGeometry.SheafOfModules.sheafTensorRight_map_globalSectionToEnd`), multiplication by a
global section is an endomorphism of the *identity* functor of `Mod(O)` and therefore commutes
with every morphism of sheaves of modules, and over `O'` it is multiplication by the monomial in
the images of the `f_i` (`restrictScalars_map_koszulScalar`).  That one square
(`sheafTensorRightUnitIso_koszulScalar_naturality`) serves both the naturality in `S` and the
compatibility with the maps between successive Koszul powers, so
`koszulPowerFunctorSystemBaseChangeIso` identifies the two sequential diagrams; both functors
preserve the colimit — [Stacks, Tag 05NB] for the tensor endofunctor and
`AlgebraicGeometry.SheafOfModules.restrictScalars_preservesColimits`, available on a general site
rather than only over a scheme, for restriction of scalars, postcomposition in a functor category
preserving pointwise colimits — and
`CategoryTheory.Limits.IsColimit.coconePointsIsoOfNatIso` transports.

Then `CategoryTheory.AlternatingCech.complexMapIso` turns that natural isomorphism into an
isomorphism of complexes and, composed with `tensorExtendedAlternatingCechIso` and with
`CategoryTheory.AlternatingCech.mapComplexIso` at restriction of scalars, gives
`extendedAlternatingCechBaseChangeIso`: **the lower row is `Č(O')`**, read as a complex of
`O`-modules.

The route *not* taken is the direct one, through the termwise identification `O_f ⊗_O O' ≅ O'_{f'}`
of `AlgebraicGeometry.RingedSite.awayTensorIsoBaseChangeAwayModule` in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/DerivedCompletionRinged/AwayTensorBaseChange.lean`,
which holds at every subset as
`AlgebraicGeometry.RingedSite.awayLocalizationTensorObjIso`.  That family is a composite of three
isomorphisms of *sheafifications*, so proving it natural in `S` would mean pushing the square down
to the presheaves, where both legs compute on pure tensors, and identifying each transition map —
chosen by a universal property, see `AlgebraicGeometry.RingedSite.eq_awayTransition` — with the
sheafification of an explicit map of presheaves of localizations.  The Koszul route needs none of
that, because the systems it compares are constant.  The two isomorphisms are not compared here,
and neither subsumes the other as a statement: what the sheafification route gives and this one
does not is the explicit sectionwise formula `O(U)[1/f] ⊗_{O(U)} O'(U) ≅ O'(U)[1/f'|_U]`
(`AlgebraicGeometry.RingedSite.sectionwiseBaseChangeIso`), which is what [Stacks, Tag 099B] needs
of it over a single global section.

## The generation hypothesis

The source assumes only that `O/(f₁, …, f_r) ≅ O'/(f₁, …, f_r)O'`, so its ideal is the one
*generated* by the `f_k`: on a site that is the image of `O^r ⟶ O` taken in sheaves, whose
sections over an object are `O`-linear combinations of the `f_k` only after restriction along
the arrows of a covering sieve.  `IsLocallyGeneratedBySections` is that condition, and it is
what the theorem below assumes.  The sectionwise condition of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FlatNeighbourhoodQuasiIso.lean` — every section of
`I` over every object is a combination of the `f_k` *there* — is strictly stronger, and
assuming it would exclude the instance the source is about.

Locality costs one step: a product of `r * N + 1` sections of `I` annihilates a section of a
cohomology sheaf only after restriction along a common refinement of `r * N + 1` covering
sieves, and the conclusion is pulled back from that refinement because a sheaf of modules is
separated.

## References

* [Stacks Project, Tag 099H](https://stacks.math.columbia.edu/tag/099H)
* [Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
* [Stacks Project, Tag 0663](https://stacks.math.columbia.edu/tag/0663)
* [Stacks Project, Tag 0GLY](https://stacks.math.columbia.edu/tag/0GLY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open AlgebraicGeometry AlgebraicGeometry.SheafOfModules AlgebraicGeometry.RingedSite

universe u

namespace Stacks.Sheaves.FlatNeighbourhood

universe v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J AddCommGrpCat.{w}]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] in
/-- **A finite family of covering sieves is refined by a single covering sieve**, namely their
intersection: the intersection of two covering sieves covers, and the empty intersection is the
maximal sieve. -/
@[sga "4 II 1.1.1" "special case"]
theorem exists_covering_sieve_le {Y : C} {n : ℕ} (T : Fin n → Sieve Y) (hT : ∀ j, T j ∈ J Y) :
    ∃ S ∈ J Y, ∀ j, S ≤ T j := by
  induction n with
  | zero => exact ⟨⊤, J.top_mem Y, fun j ↦ j.elim0⟩
  | succ n ih =>
    obtain ⟨S, hS, hle⟩ := ih (fun j ↦ T j.succ) fun j ↦ hT j.succ
    exact ⟨T 0 ⊓ S, J.intersection_covering (hT 0) hS,
      Fin.cases inf_le_left fun j ↦ inf_le_right.trans (hle j)⟩

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] in
/-- **The pigeonhole step of the proof of [Stacks, Tag 099H], over one object.**  Let the `a_k`
kill the sections of `F` to the power `N`, and let `b₁, …, b_{rN+1}` be sections of `I` over `Y`
which are `O`-linear combinations of the `a_k` *there*.  Then their product annihilates every
section of `F` over `Y`.

A product of `r * N + 1` such sections expands into a sum of monomials in the `a_k` of degree
`r * N + 1`, and in each monomial some `a_k` occurs more than `N` times by the pigeonhole
principle, so that the monomial is divisible by `a_k ^ N`. -/
theorem prod_smul_eq_zero_of_exists_sections {O : Sheaf J CommRingCat.{w}}
    {I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (i : I ⟶ RingModule O)
    {r : ℕ} (a : Fin r → Stacks.Sheaves.KoszulGlobalSections.GlobalSection O)
    {F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)} {N : ℕ}
    (hF : ∀ (k : Fin r) (Y : Cᵒᵖ) (x : F.val.obj Y),
      (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj Y from (a k).val Y) ^ N • x = 0)
    (Y : Cᵒᵖ) (b : Fin (r * N + 1) → I.val.obj Y) (x : F.val.obj Y)
    (hb : ∀ j, ∃ c : Fin r → (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj Y,
      (i.val.app Y (b j) : (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj Y) =
        ∑ k, c k * (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj Y from (a k).val Y)) :
    (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj Y from
      (Finset.univ.prod (fun j ↦ show O.obj.obj Y from (i.val.app Y) (b j)) :
        O.obj.obj Y)) • x = 0 := by
  classical
  let : CommRing ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj Y) :=
    inferInstanceAs (CommRing (O.obj.obj Y))
  choose c hc using hb
  change ((Finset.univ.prod (fun j ↦ (i.val.app Y) (b j)) :
    (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj Y)) • x = 0
  have hkey : ∀ σ : Fin (r * N + 1) → Fin r,
      (∏ j, (c j (σ j) *
        (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj Y from
          (a (σ j)).val Y))) • x = 0 := by
    intro σ
    obtain ⟨k, -, hk⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := (Finset.univ : Finset (Fin (r * N + 1)))) (t := (Finset.univ : Finset (Fin r)))
      (f := σ) (n := N) (fun j _ ↦ Finset.mem_univ _) (by simp)
    have hfib : ∏ j ∈ Finset.univ with σ j = k,
          (c j (σ j) *
            (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj Y from (a (σ j)).val Y)) =
        (∏ j ∈ Finset.univ with σ j = k, c j (σ j)) *
          (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj Y from (a k).val Y) ^
            (Finset.univ.filter (fun j ↦ σ j = k)).card := by
      rw [Finset.prod_mul_distrib]
      congr 1
      rw [Finset.prod_congr rfl (fun j hj ↦ by rw [(Finset.mem_filter.mp hj).2]),
        Finset.prod_const]
    obtain ⟨wit, hwit⟩ :
        (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj Y from (a k).val Y) ^ N ∣
          ∏ j, (c j (σ j) *
            (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj Y from (a (σ j)).val Y)) := by
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j ↦ σ j = k), hfib]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (pow_dvd_pow _ hk.le) _) _
    rw [hwit, mul_smul]
    exact hF k Y (wit • x)
  simp only [hc]
  rw [Finset.prod_univ_sum, Finset.sum_smul]
  exact Finset.sum_eq_zero fun σ _ ↦ hkey σ

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] in
/-- **A module all of whose sections are killed by a fixed power of each generator of `I` is
annihilated by a power of `I`.**  This is the step "these sheaves are annihilated by
`f_1^n, …, f_r^n`, hence by `(f_1, …, f_r)^m` for some `m ≫ 0`" of the proof of
[Stacks, Tag 099H], in the shape Tag 0GLY consumes.

Generation of `I` by the `a_k` is only needed *locally*: every section of `I` is required to be
an `O`-linear combination of the `a_k` after restriction along the arrows of some covering
sieve, which is what the ideal sheaf generated by `a₁, …, a_r` satisfies.  The product of
`r * N + 1` sections of `I` therefore annihilates a section of `F` only after restriction along
a common refinement of finitely many covering sieves; `F` is a sheaf, hence separated, so the
section it annihilates is already zero. -/
theorem isAnnihilatedByPow_of_pow_smul_eq_zero {O : Sheaf J CommRingCat.{w}}
    {I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (i : I ⟶ RingModule O)
    {r : ℕ} (a : Fin r → Stacks.Sheaves.KoszulGlobalSections.GlobalSection O)
    (hgen : ∀ (Y : Cᵒᵖ) (t : I.val.obj Y), ∃ S ∈ J Y.unop,
      ∀ ⦃Z : C⦄ (g : Z ⟶ Y.unop), S g →
        ∃ c : Fin r → (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj (Opposite.op Z),
          (i.val.app (Opposite.op Z) (I.val.map g.op t) :
              (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj (Opposite.op Z)) =
            ∑ k, c k * (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj (Opposite.op Z) from
              (a k).val (Opposite.op Z)))
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (N : ℕ)
    (hF : ∀ (k : Fin r) (Y : Cᵒᵖ) (x : F.val.obj Y),
      (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj Y from (a k).val Y) ^ N • x = 0) :
    IsAnnihilatedByPow i F := by
  classical
  refine ⟨r * N + 1, fun Y b x ↦ ?_⟩
  choose T hT hdec using fun j : Fin (r * N + 1) ↦ hgen Y (b j)
  obtain ⟨S, hS, hSle⟩ := exists_covering_sieve_le T hT
  have hloc : ∀ ⦃Z : C⦄ (g : Z ⟶ Y.unop), S g →
      F.val.map g.op ((show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj Y from
          (Finset.univ.prod (fun j ↦ show O.obj.obj Y from (i.val.app Y) (b j)) :
            O.obj.obj Y)) • x) =
        F.val.map g.op (0 : F.val.obj Y) := by
    intro Z g hg
    have key := prod_smul_eq_zero_of_exists_sections i a hF (Opposite.op Z)
      (fun j ↦ I.val.map g.op (b j)) (F.val.map g.op x) fun j ↦ hdec j g (hSle j _ hg)
    have hnat : ∀ j, (show O.obj.obj (Opposite.op Z) from
          (i.val.app (Opposite.op Z)) (I.val.map g.op (b j))) =
        (O.obj.map g.op).hom (show O.obj.obj Y from (i.val.app Y) (b j)) :=
      fun j ↦ PresheafOfModules.naturality_apply i.val g.op (b j)
    rw [Finset.prod_congr rfl fun j _ ↦ hnat j, ← map_prod] at key
    rwa [map_zero, PresheafOfModules.map_smul]
  exact F.isSheaf.isSeparated Y.unop S hS _ 0 fun _ g hg ↦ hloc g hg

/-- A natural transformation which is invertible at every object of a diagram is invertible at
the colimit of that diagram, provided both functors take the colimit cocone to a colimit
cocone. -/
theorem isIso_app_of_isColimit {A B : Type*} [Category* A] [Category* B] {K : Type*}
    [Category* K] {Fn Gn : A ⥤ B} (τ : Fn ⟶ Gn) {D : K ⥤ A} {c : Limits.Cocone D}
    (hF : Limits.IsColimit (Fn.mapCocone c)) (hG : Limits.IsColimit (Gn.mapCocone c))
    (h : ∀ k, IsIso (τ.app (D.obj k))) : IsIso (τ.app c.pt) := by
  let α : D ⋙ Fn ≅ D ⋙ Gn :=
    NatIso.ofComponents (fun k ↦ @asIso _ _ _ _ (τ.app (D.obj k)) (h k))
      fun g ↦ τ.naturality (D.map g)
  have key : τ.app c.pt = (Limits.IsColimit.coconePointsIsoOfNatIso hF hG α).hom := by
    refine hF.hom_ext fun k ↦ ?_
    rw [Limits.IsColimit.comp_coconePointsIsoOfNatIso_hom]
    exact τ.naturality (c.ι.app k)
  rw [key]
  infer_instance

end Stacks.Sheaves.FlatNeighbourhood

namespace Stacks.Sheaves.CechFlatNeighbourhood

section Helpers

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}]

/-- The `m`-th power of a global section of the structure sheaf, as a compatible family of
local sections of the underlying sheaf of rings. -/
def powSection (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) (m : ℕ) :
    KoszulGlobalSections.GlobalSection X.O :=
  ⟨fun U ↦ globalSectionVal h U ^ m, by
    intro U V g
    change (X.O.obj.map g).hom (globalSectionVal h U ^ m) = globalSectionVal h V ^ m
    rw [map_pow, globalSectionVal_map]⟩

omit [HasWeakSheafify X.J CommRingCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] in
/-- The section of `powSection X h m` over `U` is the `m`-th power of the section of `h` over
`U`. -/
@[simp] theorem powSection_val (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
    (m : ℕ) (U : X.Cᵒᵖ) : (powSection X h m).val U = globalSectionVal h U ^ m := rfl

/-- A global section of the structure sheaf, as a compatible family of local sections of the
underlying sheaf of rings. -/
def genSection (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) :
    KoszulGlobalSections.GlobalSection X.O :=
  ⟨fun U ↦ globalSectionVal h U, fun g ↦ globalSectionVal_map h g⟩

omit [HasWeakSheafify X.J CommRingCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] in
/-- The section of `genSection X h` over `U` is the section of `h` over `U`. -/
@[simp] theorem genSection_val (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
    (U : X.Cᵒᵖ) : (genSection X h).val U = globalSectionVal h U := rfl

variable {r : ℕ} (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- The family of `(n+1)`-st powers of the chosen global sections. -/
abbrev powFamily (n : ℕ) : Fin r → KoszulGlobalSections.GlobalSection X.O :=
  fun i ↦ powSection X (f i) (n + 1)

/-- The chosen global sections, as a family of compatible families of local sections. -/
abbrev genFamily : Fin r → KoszulGlobalSections.GlobalSection X.O := fun i ↦ genSection X (f i)

omit [HasWeakSheafify X.J CommRingCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] in
/-- The Koszul system of the `(n+1)`-st powers, as built from global sections, is the Koszul
power system of `AlgebraicGeometry.RingedSite.koszulPowerFunctor`. -/
theorem koszulFunctor_powFamily_eq (n : ℕ) :
    KoszulGlobalSections.koszulFunctor X.O (powFamily X f n) = koszulPowerFunctor X f n := by
  refine CategoryTheory.Functor.ext (fun S ↦ rfl) fun S T g ↦ ?_
  simp only
  change (KoszulGlobalSections.smulEnd X.O
      (KoszulGlobalSections.prodSection X.O (powFamily X f n) (T \ S))).asHom.app _ =
    koszulScalar X f (koszulExp n S T)
  refine congrArg (fun a ↦ (KoszulGlobalSections.smulEnd X.O a).asHom.app _)
    (Subtype.ext (funext ?_))
  intro U
  have hexp : ∀ i : Fin r, koszulExp n S T i = if i ∈ T \ S then n + 1 else 0 := fun _ ↦ rfl
  change ∏ i ∈ T \ S, globalSectionVal (f i) U ^ (n + 1) =
    ∏ i, globalSectionVal (f i) U ^ (koszulExp n S T i)
  rw [← Finset.prod_subset (Finset.subset_univ (T \ S))
    (fun i _ hi ↦ by rw [hexp i, ite_eq_right hi, pow_zero])]
  exact Finset.prod_congr rfl fun i hi ↦ by rw [hexp i, ite_eq_left hi]

omit [HasWeakSheafify X.J CommRingCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] in
/-- The Koszul complex of the `(n+1)`-st powers of the chosen global sections is the `n`-th
Koszul power complex of `AlgebraicGeometry.RingedSite.koszulPowerComplex`. -/
theorem koszulComplex_powFamily_eq (n : ℕ) :
    KoszulGlobalSections.koszulComplex X.O (powFamily X f n) = koszulPowerComplex X f n :=
  congrArg AlternatingCech.complex (koszulFunctor_powFamily_eq X f n)

end Helpers

section Main

open Stacks.Sheaves.FlatNeighbourhood

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}]
  [HasWeakSheafify J CommRingCat.{u}]

/-- The ringed site with underlying site `(C, J)` and structure sheaf `O`.  The extended
alternating Čech complex is built for a ringed site, while extension of scalars along a
morphism of sheaves of rings is built for a bare sheaf of commutative rings on a site; this is
the passage from the second setting to the first. -/
abbrev ringedSite (O : Sheaf J CommRingCat.{u}) : RingedSite.{u, u, u} where
  C := C
  J := J
  O := O

variable (O : Sheaf J CommRingCat.{u}) {r : ℕ}
  (f : Fin r → Presheaf.globalSections (O.obj ⋙ forget CommRingCat.{u}))
  {O' : Sheaf J CommRingCat.{u}} (φ : O ⟶ O')
  [PreservesFiniteLimits (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
    (RestrictedRingModule φ)))]
  {I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
  (i : I ⟶ RingModule O) [Mono i]
  (e : cokernel i ≅
    cokernel ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
      (RestrictedRingModule φ))).map i))
  (he : cokernel.π i ≫ e.hom = (tensorUnitMap φ (RingModule O)).val ≫
    cokernel.π ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
      (RestrictedRingModule φ))).map i))

/-- The ideal sheaf `I` is contained in the ideal sheaf generated by the global sections
`f₁, …, f_r`: every section of `I` is, after restriction along the arrows of some covering
sieve, an `O`-linear combination of the `f_k`.  This is what `I = (f₁, …, f_r)` gives on a
general site, where the ideal generated by a family of sections is the *sheaf* image of
`O^r ⟶ O` and its sections are combinations of the `f_k` only locally. -/
abbrev IsLocallyGeneratedBySections : Prop :=
  ∀ (Y : Cᵒᵖ) (t : I.val.obj Y), ∃ S ∈ J Y.unop,
    ∀ ⦃Z : C⦄ (g : Z ⟶ Y.unop), S g →
      ∃ c : Fin r → (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj (Opposite.op Z),
        (i.val.app (Opposite.op Z) (I.val.map g.op t) :
            (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj (Opposite.op Z)) =
          ∑ k, c k * (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj (Opposite.op Z) from
            globalSectionVal (X := ringedSite O) (f k) (Opposite.op Z))

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [PreservesFiniteLimits
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
      (RestrictedRingModule φ)))] [Mono i] [HasWeakSheafify J CommRingCat.{u}] in
/-- **Every cohomology sheaf of the Koszul complex on the `(n+1)`-st powers of `f₁, …, f_r` is
annihilated by a power of `I`.**  Each `f_k^{n+1}` acts as zero on that cohomology, by the
null-homotopy of [Stacks, Tag 0663] on a site, and the pigeonhole step
`Stacks.Sheaves.FlatNeighbourhood.isAnnihilatedByPow_of_pow_smul_eq_zero` turns that into
annihilation by the power `r * (n + 1) + 1` of the ideal generated by the `f_k`. -/
theorem isAnnihilatedByPow_homology_koszulPowerComplex
    (hgen : IsLocallyGeneratedBySections O f i) (n : ℕ) (p : ℤ) :
    IsAnnihilatedByPow i ((koszulPowerComplex (ringedSite O) f n).homology p) := by
  have h := isAnnihilatedByPow_of_pow_smul_eq_zero i (genFamily (ringedSite O) f) hgen
    ((KoszulGlobalSections.koszulComplex O (powFamily (ringedSite O) f n)).homology p) (n + 1)
    (fun k Y x ↦
      KoszulGlobalSections.smul_homology_eq_zero O (powFamily (ringedSite O) f n) k p Y x)
  rwa [koszulComplex_powFamily_eq (ringedSite O) f n] at h

/-- **The lower row of the source's square is the extended alternating Čech complex of the
system `S ↦ 𝒪_{f_S} ⊗_𝒪 𝒪'`.**  Extension of scalars along `φ`, applied degreewise to
`Č(f)`, is the extended alternating Čech complex of the system of subsets of `Fin r` whose
value at `S` is `𝒪_{f_S} ⊗_𝒪 𝒪'` and whose transition maps are the base changes of the
localization maps.

This is `CategoryTheory.AlternatingCech.mapComplexIso` at the tensor endofunctor: it preserves
the finite products `∏_{|S| = p} 𝒪_{f_S}` that form the terms, by the hypothesis
`PreservesFiniteLimits`, and it commutes with the alternating differential because that
differential is a `ℤ`-linear combination of transition maps and the functor is additive. -/
def tensorExtendedAlternatingCechIso :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
          (RestrictedRingModule φ))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (extendedAlternatingCech (ringedSite O) f) ≅
      AlternatingCech.complex
        (awayLocalizationFunctor (ringedSite O) f ⋙
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
            (RestrictedRingModule φ))) :=
  letI : Functor.Additive (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
      (RestrictedRingModule φ))) :=
    Functor.additive_of_preserves_binary_products _
  AlternatingCech.mapComplexIso _ _

/-! ### The lower row is the extended alternating Čech complex of `O'` -/

section BaseChange

omit [PreservesFiniteLimits
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
      (RestrictedRingModule φ)))]

/-- The rings of sections of a sheaf of commutative rings are commutative. This instance is
stated directly at the sheaf of commutative rings, with the canonical
`Stacks.SheafOfModules.Tensor.ringSheaf` coefficient index. -/
local instance isMulCommutative_underlyingRingSheafOfSite_obj (A : Sheaf J CommRingCat.{u})
    (U : Cᵒᵖ) : IsMulCommutative ((Stacks.SheafOfModules.Tensor.ringSheaf A).obj.obj U) := by
  change IsMulCommutative (A.obj.obj U)
  infer_instance

/-- The images in `O'` of the chosen global sections of `O`. -/
abbrev baseChangeFamily (k : Fin r) :
    Presheaf.globalSections (O'.obj ⋙ forget CommRingCat.{u}) :=
  baseChangeGlobalSection (ringedSite O) O' φ (f k)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  [HasWeakSheafify J CommRingCat.{u}] in
/-- `φ` carries the monomial `∏ᵢ fᵢ^{eᵢ}` to the monomial with the same exponents in the
images of the `f_i`. -/
theorem koszulValue_baseChangeFamily (e : Fin r → ℕ) (U : Cᵒᵖ) :
    koszulValue (ringedSite O') (baseChangeFamily O f φ) e U =
      (φ.hom.app U).hom (koszulValue (ringedSite O) f e U) := by
  rw [koszulValue, koszulValue, map_prod]
  exact Finset.prod_congr rfl fun k _ => by
    rw [map_pow, globalSectionVal_baseChangeGlobalSection]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  [HasWeakSheafify J CommRingCat.{u}] in
/-- **Multiplication by a monomial in the images of the `f_i`, read over `O`, is multiplication
by the monomial in the `f_i` itself.** -/
theorem restrictScalars_map_koszulScalar (e : Fin r → ℕ) :
    (SheafOfModules.restrictScalars (baseChangeRingSheafMap (ringedSite O) O' φ)).map
        (koszulScalar (ringedSite O') (baseChangeFamily O f φ) e) =
      (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf O)
        (koszulFamily (ringedSite O) f e)).asHom.app (RestrictedRingModule φ) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
  change koszulRingValue (ringedSite O') (baseChangeFamily O f φ) e U •
        (show (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite O').O)).val.obj U from t) =
      koszulRingValue (ringedSite O) f e U • t
  rw [show koszulRingValue (ringedSite O') (baseChangeFamily O f φ) e U =
      (φ.hom.app U).hom (koszulRingValue (ringedSite O) f e U) from
    koszulValue_baseChangeFamily O f φ e U]
  rfl

omit [HasWeakSheafify J CommRingCat.{u}] in
/-- **The square that makes the base change of the Koszul systems natural.**  The tensor
endofunctor carries multiplication by the monomial `∏ᵢ fᵢ^{eᵢ}` to multiplication by it
(`AlgebraicGeometry.SheafOfModules.sheafTensorRight_map_globalSectionToEnd`), multiplication by a
global section is an endomorphism of the *identity* functor of `Mod(O)` and so commutes with
`O ⊗_O O' ≅ O'`, and over `O'` that multiplication is multiplication by the monomial in the
images of the `f_i`. -/
theorem sheafTensorRightUnitIso_koszulScalar_naturality (e : Fin r → ℕ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
        (RestrictedRingModule φ))).map (koszulScalar (ringedSite O) f e) ≫
        (sheafTensorRightUnitIso O (RestrictedRingModule φ)).hom =
      (sheafTensorRightUnitIso O (RestrictedRingModule φ)).hom ≫
        (SheafOfModules.restrictScalars (baseChangeRingSheafMap (ringedSite O) O' φ)).map
          (koszulScalar (ringedSite O') (baseChangeFamily O f φ) e) :=
  (congrArg
    (fun scalarMap => scalarMap ≫ (sheafTensorRightUnitIso O (RestrictedRingModule φ)).hom)
    (sheafTensorRight_map_globalSectionToEnd O (RestrictedRingModule φ)
      (koszulFamily (ringedSite O) f e)
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)))).trans
    (((Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf O)
      (koszulFamily (ringedSite O) f e)).asHom.naturality
        (sheafTensorRightUnitIso O (RestrictedRingModule φ)).hom).symm.trans
      (congrArg
        (fun scalarMap => (sheafTensorRightUnitIso O (RestrictedRingModule φ)).hom ≫ scalarMap)
        (restrictScalars_map_koszulScalar O f φ e).symm))

/-- **The base change of the Koszul system on the `(n+1)`-st powers of `f₁, …, f_r` is the
Koszul system on the `(n+1)`-st powers of their images**, read over `O`.  Both systems are
constant — at `O` on one side and at `O'` on the other — so the comparison is the single
isomorphism `O ⊗_O O' ≅ O'` at every subset, and its naturality is
`sheafTensorRightUnitIso_koszulScalar_naturality` at the exponent vector of the transition
map. -/
def koszulPowerFunctorBaseChangeIso (n : ℕ) :
    koszulPowerFunctor (ringedSite O) f n ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
          (RestrictedRingModule φ)) ≅
      koszulPowerFunctor (ringedSite O') (baseChangeFamily O f φ) n ⋙
        SheafOfModules.restrictScalars (baseChangeRingSheafMap (ringedSite O) O' φ) :=
  NatIso.ofComponents (fun _ => sheafTensorRightUnitIso O (RestrictedRingModule φ))
    fun _ => sheafTensorRightUnitIso_koszulScalar_naturality O f φ _

omit [HasWeakSheafify J CommRingCat.{u}] in
/-- The comparison is compatible with the maps between successive Koszul powers, which at the
subset `S` are again multiplications by a monomial. -/
theorem whiskerRight_koszulPowerTrans_comp_koszulPowerFunctorBaseChangeIso (n : ℕ) :
    Functor.whiskerRight (koszulPowerTrans (ringedSite O) f n)
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
            (RestrictedRingModule φ))) ≫
        (koszulPowerFunctorBaseChangeIso O f φ (n + 1)).hom =
      (koszulPowerFunctorBaseChangeIso O f φ n).hom ≫
        Functor.whiskerRight (koszulPowerTrans (ringedSite O') (baseChangeFamily O f φ) n)
          (SheafOfModules.restrictScalars (baseChangeRingSheafMap (ringedSite O) O' φ)) :=
  NatTrans.ext (funext fun _ =>
    sheafTensorRightUnitIso_koszulScalar_naturality O f φ _)

/-- **The base change of the sequential diagram of Koszul systems is the sequential diagram of
Koszul systems over `O'`**, read over `O`.  A morphism of `ℕ`-indexed diagrams is determined by
its squares at `n ⟶ n + 1` (`CategoryTheory.NatTrans.ofSequence`), and those are
`whiskerRight_koszulPowerTrans_comp_koszulPowerFunctorBaseChangeIso`. -/
def koszulPowerFunctorSystemBaseChangeMap :
    koszulPowerFunctorSystem (ringedSite O) f ⋙
        (Functor.whiskeringRight (Finset (Fin r))
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))).obj
            (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
              (RestrictedRingModule φ))) ⟶
      koszulPowerFunctorSystem (ringedSite O') (baseChangeFamily O f φ) ⋙
        (Functor.whiskeringRight (Finset (Fin r))
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))).obj
            (SheafOfModules.restrictScalars (baseChangeRingSheafMap (ringedSite O) O' φ)) :=
  NatTrans.ofSequence (fun n => (koszulPowerFunctorBaseChangeIso O f φ n).hom) fun n => by
    rw [Functor.comp_map, Functor.comp_map, koszulPowerFunctorSystem_map_succ,
      koszulPowerFunctorSystem_map_succ]
    exact whiskerRight_koszulPowerTrans_comp_koszulPowerFunctorBaseChangeIso O f φ n

omit [HasWeakSheafify J CommRingCat.{u}] in
/-- The component at `n` of `koszulPowerFunctorSystemBaseChangeMap` is the comparison
`koszulPowerFunctorBaseChangeIso` at `n`. -/
@[simp]
theorem koszulPowerFunctorSystemBaseChangeMap_app (n : ℕ) :
    (koszulPowerFunctorSystemBaseChangeMap O f φ).app n =
      (koszulPowerFunctorBaseChangeIso O f φ n).hom :=
  NatTrans.ofSequence_app _ _ n

/-- The comparison map `koszulPowerFunctorSystemBaseChangeMap` is an isomorphism of diagrams. -/
instance isIso_koszulPowerFunctorSystemBaseChangeMap :
    IsIso (koszulPowerFunctorSystemBaseChangeMap O f φ) := by
  have : ∀ n, IsIso ((koszulPowerFunctorSystemBaseChangeMap O f φ).app n) := fun n => by
    rw [koszulPowerFunctorSystemBaseChangeMap_app]
    exact (koszulPowerFunctorBaseChangeIso O f φ n).isIso_hom
  exact NatIso.isIso_of_isIso_app _

/-- The same comparison as an isomorphism of diagrams. -/
def koszulPowerFunctorSystemBaseChangeIso :
    koszulPowerFunctorSystem (ringedSite O) f ⋙
        (Functor.whiskeringRight (Finset (Fin r))
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))).obj
            (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
              (RestrictedRingModule φ))) ≅
      koszulPowerFunctorSystem (ringedSite O') (baseChangeFamily O f φ) ⋙
        (Functor.whiskeringRight (Finset (Fin r))
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))).obj
            (SheafOfModules.restrictScalars (baseChangeRingSheafMap (ringedSite O) O' φ)) :=
  asIso (koszulPowerFunctorSystemBaseChangeMap O f φ)

/-- **Tensoring with `O'` preserves the colimit presentation of the Čech system.**  Colimits in
a category of functors are computed subset by subset, and the tensor endofunctor preserves
sequential colimits by [Stacks, Tag 05NB]. -/
def isColimitTensorKoszulPowerFunctorCocone :
    IsColimit (((Functor.whiskeringRight (Finset (Fin r))
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))).obj
            (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
              (RestrictedRingModule φ)))).mapCocone
      (koszulPowerFunctorCocone (ringedSite O) f)) := by
  have : PreservesColimitsOfSize.{u, u}
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
        (RestrictedRingModule φ))) :=
    Stacks.SheafOfModules.FlatSheafification.sheafTensorRight_preservesColimits J O
      (RestrictedRingModule φ)
  have : PreservesColimitsOfSize.{0, 0}
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
        (RestrictedRingModule φ))) :=
    preservesSmallestColimits_of_preservesColimits _
  exact isColimitOfPreserves _ (isColimitKoszulPowerFunctorCocone (ringedSite O) f)

/-- **Restriction of scalars along `φ` preserves the colimit presentation of the Čech system of
`O'`.**  Colimits in a category of functors are computed subset by subset, and restriction of
scalars preserves all colimits. -/
def isColimitRestrictKoszulPowerFunctorCocone :
    IsColimit (((Functor.whiskeringRight (Finset (Fin r))
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))).obj
            (SheafOfModules.restrictScalars
              (baseChangeRingSheafMap (ringedSite O) O' φ))).mapCocone
      (koszulPowerFunctorCocone (ringedSite O') (baseChangeFamily O f φ))) := by
  have : PreservesColimitsOfSize.{u, u} (SheafOfModules.restrictScalars.{u}
      (baseChangeRingSheafMap (ringedSite O) O' φ)) :=
    AlgebraicGeometry.SheafOfModules.restrictScalars_preservesColimits _
  have : PreservesColimitsOfSize.{0, 0} (SheafOfModules.restrictScalars.{u}
      (baseChangeRingSheafMap (ringedSite O) O' φ)) :=
    preservesSmallestColimits_of_preservesColimits _
  exact isColimitOfPreserves _
    (isColimitKoszulPowerFunctorCocone (ringedSite O') (baseChangeFamily O f φ))

/-- **`𝒪_{f_S} ⊗_𝒪 𝒪' ≅ 𝒪'_{f'_S}`, naturally in `S`.**  Both systems are the colimit of the
Koszul systems on the positive powers of the `f_i` — over `O` by
`AlgebraicGeometry.RingedSite.isColimitKoszulPowerFunctorCocone` and over `O'` by the same
statement there, each carried along the functor in question, which preserves that colimit — and
`koszulPowerFunctorSystemBaseChangeIso` identifies the two sequential diagrams. -/
def awayLocalizationBaseChangeIso :
    awayLocalizationFunctor (ringedSite O) f ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
          (RestrictedRingModule φ)) ≅
      awayLocalizationFunctor (ringedSite O') (baseChangeFamily O f φ) ⋙
        SheafOfModules.restrictScalars (baseChangeRingSheafMap (ringedSite O) O' φ) :=
  IsColimit.coconePointsIsoOfNatIso (isColimitTensorKoszulPowerFunctorCocone O f φ)
    (isColimitRestrictKoszulPowerFunctorCocone O f φ)
    (koszulPowerFunctorSystemBaseChangeIso O f φ)

end BaseChange

section BaseChangeComplex

/-- **The lower row of the source's square is the extended alternating Čech complex of `O'`.**

Degreewise, extension of scalars applied to `Č(f)` is the extended alternating Čech complex of
the system `S ↦ O_{f_S} ⊗_O O'` (`tensorExtendedAlternatingCechIso`); that system is the system
`S ↦ O'_{f'_S}` of localizations of `O'` read over `O` (`awayLocalizationBaseChangeIso`), so
`CategoryTheory.AlternatingCech.complexMapIso` turns the comparison into an isomorphism of
complexes; and restriction of scalars, being additive and product-preserving, commutes with the
formation of the extended alternating Čech complex
(`CategoryTheory.AlternatingCech.mapComplexIso`). -/
def extendedAlternatingCechBaseChangeIso :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
          (RestrictedRingModule φ))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (extendedAlternatingCech (ringedSite O) f) ≅
      ((SheafOfModules.restrictScalars
            (baseChangeRingSheafMap (ringedSite O) O' φ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (extendedAlternatingCech (ringedSite O') (baseChangeFamily O f φ)) :=
  letI : (SheafOfModules.restrictScalars
      (baseChangeRingSheafMap (ringedSite O) O' φ)).Additive :=
    SheafOfModules.instAdditiveRestrictScalars _
  (tensorExtendedAlternatingCechIso O f φ).trans
    ((AlternatingCech.complexMapIso (awayLocalizationBaseChangeIso O f φ)).trans
      (AlternatingCech.mapComplexIso (SheafOfModules.restrictScalars
          (baseChangeRingSheafMap (ringedSite O) O' φ))
        (awayLocalizationFunctor (ringedSite O') (baseChangeFamily O f φ))).symm)

/-- **The comparison of the two rows of the source's square**: a map from the extended
alternating Čech complex of `f₁, …, f_r` over `O` to the extended alternating Čech complex of
their images over `O'`, read as a complex of `O`-modules.  It is extension of scalars applied
degreewise, followed by the identification `extendedAlternatingCechBaseChangeIso` of the lower
row with `Č(O')`. -/
def extendedAlternatingCechBaseChangeMap :
    extendedAlternatingCech (ringedSite O) f ⟶
      ((SheafOfModules.restrictScalars
            (baseChangeRingSheafMap (ringedSite O) O' φ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (extendedAlternatingCech (ringedSite O') (baseChangeFamily O f φ)) :=
  tensorUnitComplexMap φ (extendedAlternatingCech (ringedSite O) f) ≫
    (extendedAlternatingCechBaseChangeIso O f φ).hom

end BaseChangeComplex

include he in
/-- **The comparison of [Stacks, Tag 099H] is a quasi-isomorphism**, in the general form the
proof needs.  Let `C` be a site, let `φ : O ⟶ O'` be a flat morphism of
sheaves of commutative rings on `C` which is an isomorphism modulo the ideal sheaf `I`, and let
`f₁, …, f_r` be global sections of `O` generating `I`, in the sense that every section of `I` is
locally an `O`-linear combination of them.  Then extension of scalars
along `φ`, applied degreewise, is a quasi-isomorphism on the extended alternating Čech complex

`O → ∏_{i₀} O_{f_{i₀}} → ∏_{i₀ < i₁} O_{f_{i₀} f_{i₁}} → ⋯ → O_{f_1 ⋯ f_r}`

of `f₁, …, f_r`.  Its target, the lower row of the source's square, is identified here with the
extended alternating Čech complex of the images of `f₁, …, f_r` in `O'`, read as a complex of
`O`-modules, so the comparison stated is the source's `Č(O) ⟶ Č(O')`.  The ideal `I` here need
only be contained in the ideal generated by the `f_k`; the tag itself, with `I` the ideal
generated by the `f_k`, flatness as one hypothesis, and the comparison identified with the map
induced by the canonical maps `O_{f_S} ⟶ O'_{f_S}`, is
`Stacks.Sheaves.CechFlatNeighbourhood.quasiIso_complexMap_cechSystemBaseChangeMap` in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FlatNeighbourhoodCechNatural.lean`.

The proof is the source's.  The Čech complex is the colimit of the Koszul complexes
`K(O, f₁^{n+1}, …, f_r^{n+1})` — [Stacks, Tag 0913] on a site, which is
`AlgebraicGeometry.RingedSite.isColimitKoszulCechComplexCocone`.  Cohomology commutes with
sequential colimits of sheaves of modules, filtered colimits there being exact.  Both the
identity and the tensor endofunctor preserve those colimits, so the comparison at the colimit
is the colimit of the comparisons; and on each approximant the comparison is invertible on
cohomology by [Stacks, Tag 0GLY], whose annihilation hypothesis is
`isAnnihilatedByPow_homology_koszulPowerComplex`. -/
theorem quasiIso_extendedAlternatingCechBaseChangeMap
    (hgen : IsLocallyGeneratedBySections O f i) :
    QuasiIso (extendedAlternatingCechBaseChangeMap O f φ) := by
  have : PreservesFiniteColimits
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
        (RestrictedRingModule φ))) :=
    Stacks.SheafOfModules.FlatSheafification.sheafTensorRight_preservesFiniteColimits J O
      (RestrictedRingModule φ)
  change QuasiIso (tensorUnitComplexMap φ (extendedAlternatingCech (ringedSite O) f) ≫
    (extendedAlternatingCechBaseChangeIso O f φ).hom)
  have : QuasiIso (tensorUnitComplexMap φ (extendedAlternatingCech (ringedSite O) f)) := by
    have : PreservesColimitsOfSize.{u, u}
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
          (RestrictedRingModule φ))) :=
      Stacks.SheafOfModules.FlatSheafification.sheafTensorRight_preservesColimits J O
        (RestrictedRingModule φ)
    have : PreservesColimitsOfSize.{0, 0}
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
          (RestrictedRingModule φ))) :=
      preservesSmallestColimits_of_preservesColimits _
    have := Stacks.Cohomology.DerivedLowerShriek.hasExactColimitsOfShape_nat
      (Stacks.SheafOfModules.Tensor.ringSheaf O)
    refine HomologicalComplex.quasiIso_mapNatTrans_app (tensorUnitNatTrans φ)
      (extendedAlternatingCech (ringedSite O) f) fun p ↦ ?_
    have : PreservesColimitsOfShape ℕ (HomologicalComplex.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (ComplexShape.up ℤ) p) :=
      Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor (ComplexShape.up ℤ) p
    have hc : IsColimit ((HomologicalComplex.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (ComplexShape.up ℤ)
          p).mapCocone
          (koszulCechComplexCocone (ringedSite O) f)) :=
      isColimitOfPreserves _ (isColimitKoszulCechComplexCocone (ringedSite O) f)
    have hiso : ∀ n : ℕ, IsIso ((tensorUnitNatTrans φ).app
        ((koszulPowerComplex (ringedSite O) f n).homology p)) := fun n ↦
      isIso_tensorUnitNatTrans_app_of_isAnnihilatedByPow φ i e he
        ((koszulPowerComplex (ringedSite O) f n).homology p)
        (isAnnihilatedByPow_homology_koszulPowerComplex O f i hgen n p)
    have hgoal : IsIso ((tensorUnitNatTrans φ).app ((HomologicalComplex.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (ComplexShape.up ℤ)
          p).mapCocone
          (koszulCechComplexCocone (ringedSite O) f)).pt) :=
      isIso_app_of_isColimit (tensorUnitNatTrans φ)
        (isColimitOfPreserves
          (𝟭 (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))) hc)
        (isColimitOfPreserves ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj
          (RestrictedRingModule φ)) hc) hiso
    exact hgoal
  infer_instance

end Main

end Stacks.Sheaves.CechFlatNeighbourhood

end
