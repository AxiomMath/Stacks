module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Locality of cohomology

A cohomology class of positive degree on a sheaf of `O_X`-modules vanishes after restriction to
the members of a suitable open covering.

Throughout, `X` is a ringed space, i.e. a topological space equipped with a sheaf of
commutative unital rings `O_X`, and `Mod(O_X)` denotes the abelian category of sheaves of
`O_X`-modules, which has enough injectives.

## Main definitions

* `secF R U`: the global-sections-over-`U` functor `Mod(O_X) ⥤ AddCommGrpCat`.
* `Hgroup R U n F`: the cohomology `Hⁿ(U, F)`, obtained by choosing an injective resolution
  `0 → F → I^•` in `Mod(O_X)` and taking `Hⁿ(Γ(U, I^•))`; equivalently the `n`-th right derived
  functor of `secF R U` applied to `F`.  This is independent of the resolution up to canonical
  isomorphism.
* `Hrestrict R h n F`: for `U ≤ V`, the restriction map `Hⁿ(V, F) → Hⁿ(U, F)` induced by the
  restriction maps of the resolution, functorial in `F` and independent of the resolution.

## Main results

* `locality_of_cohomology`: for `n > 0` and `ξ ∈ Hⁿ(U, F)` there is an open covering
  `U = ⨆ i, Uᵢ` with `ξ|_{Uᵢ} = 0` in `Hⁿ(Uᵢ, F)` for every `i`.

## Implementation notes

- A "ringed space" is encoded directly by its structure sheaf, a `RingCat`-valued sheaf
  `R : Sheaf (Opens.grothendieckTopology X) RingCat` on the topological space `X`. This is exactly
  the data consumed by Mathlib's `SheafOfModules R`, the abelian category
  $\mathit{Mod}(\mathcal{O}_X)$.
- `H^n(U, \mathcal{F})` is realized as the $n$-th right derived functor (`Functor.rightDerived`) of
  the global-sections-over-$U$ functor `secF R U : SheafOfModules R ⥤ AddCommGrpCat`, which is
  `SheafOfModules.toSheaf R` (forget to abelian-group sheaves) followed by evaluation at `U`. This
  computes cohomology via injective resolutions, matching Definition 1, since right derived
  functors are defined through injective resolutions and are independent of the chosen resolution.
- The restriction map (Definition 2) is obtained functorially: `sheafSections` is a functor in the
  open `U`, so `U ≤ V` induces a natural transformation `secF R V ⟶ secF R U`, and
  `NatTrans.rightDerived` transports it to `H^n(V, F) ⟶ H^n(U, F)`.
- We assume the standard hypotheses making `SheafOfModules R` an abelian category with enough
  injectives (`HasSheafify`, `WEqualsLocallyBijective`, `EnoughInjectives`), reflecting the fact
  that `Mod(O_X)` has enough injectives.

## References

* [Stacks Project, Tag 01E3](https://stacks.math.columbia.edu/tag/01E3)
-/

open CategoryTheory Opposite TopologicalSpace

universe u

variable {X : Type u} [TopologicalSpace X]
-- The structure sheaf `O_X` of the ringed space, encoded as a `RingCat`-valued sheaf.
variable (R : Sheaf (Opens.grothendieckTopology X) RingCat)
-- Standard hypotheses ensuring `Mod(O_X) = SheafOfModules R` is abelian with enough injectives.
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]
variable [EnoughInjectives (SheafOfModules R)]

-- Main Definition(s)

/-- The global-sections-over-`U` functor evaluated on abelian-group sheaves is additive. -/
instance secAdditive (U : Opens X) :
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj (op U)).Additive :=
  inferInstanceAs (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat
    ⋙ (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op U)).Additive

/-- The global-sections functor $\Gamma(U, -) : \mathit{Mod}(\mathcal{O}_X) \to \mathrm{Ab}$,
factored as the forgetful functor to abelian-group sheaves followed by evaluation at `U`. -/
@[ega "0 12.1.1" "partial", sga "4½ Arcata 1.6.5" "special case"]
noncomputable abbrev secF (U : Opens X) : SheafOfModules R ⥤ AddCommGrpCat :=
  SheafOfModules.toSheaf R ⋙ (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj (op U)

/-- The global-sections functor `secF R U` is additive. -/
instance secFAdditive (U : Opens X) : (secF R U).Additive := by
  unfold secF; infer_instance

/-- Cohomology functor `H^n(U, -) : Mod(O_X) ⥤ Ab`, the `n`-th right derived functor of
$\Gamma(U, -)$ (Definition 1). Right derived functors are computed via injective resolutions and
are independent of the chosen resolution. -/
@[ega "0 12.1.1", sga "4 V 2.4.1" "special case", sga "4½ Cycle 1.1.3" "special case"]
noncomputable abbrev Hfunctor (U : Opens X) (n : ℕ) : SheafOfModules R ⥤ AddCommGrpCat :=
  (secF R U).rightDerived n

/-- The cohomology group `H^n(U, F)`. -/
@[ega "0 12.1.1",
  sga "3 III 4.5" "R¹Γ(Y₀",
  sga "4 V 2.4.1" "special case",
  sga "4½ Cycle 1.1.3" "special case"]
noncomputable abbrev Hgroup (U : Opens X) (n : ℕ) (F : SheafOfModules R) : AddCommGrpCat :=
  (Hfunctor R U n).obj F

/-- The restriction natural transformation `Γ(V, -) ⟶ Γ(U, -)` for `U ≤ V`, induced by the
functoriality of `sheafSections` in the open. -/
noncomputable def secRestrict {U V : Opens X} (h : U ≤ V) : secF R V ⟶ secF R U :=
  Functor.whiskerLeft (SheafOfModules.toSheaf R)
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).map (homOfLE h).op)

/-- Restriction on cohomology functors `H^n(V, -) ⟶ H^n(U, -)` for `U ≤ V`. -/
noncomputable def HrestrictNT {U V : Opens X} (h : U ≤ V) (n : ℕ) :
    Hfunctor R V n ⟶ Hfunctor R U n :=
  NatTrans.rightDerived (secRestrict R h) n

/-- The restriction map on cohomology groups `H^n(V, F) ⟶ H^n(U, F)` (Definition 2). -/
noncomputable def Hrestrict {U V : Opens X} (h : U ≤ V) (n : ℕ) (F : SheafOfModules R) :
    Hgroup R V n F ⟶ Hgroup R U n F :=
  (HrestrictNT R h n).app F

/-- The complex of global sections over an open `W` of the injective resolution `I` of `F`,
i.e. `Γ(W, I^•)` realized as `(secF R W).mapHomologicalComplex` applied to `I.cocomplex`. Its
degree-`n` homology is canonically isomorphic to `H^n(W, F) = Hgroup R W n F` via
`InjectiveResolution.isoRightDerivedObj`. -/
noncomputable abbrev secCx {F : SheafOfModules R} (I : InjectiveResolution F) (W : Opens X) :
    CochainComplex AddCommGrpCat ℕ :=
  ((secF R W).mapHomologicalComplex _).obj I.cocomplex

-- Auxiliary lemmas for the proof of Tag 01E3

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat] in
/-- **Cover extraction from a covering sieve.**
A sieve `S` on an open `U` of a topological space is a covering sieve for
`Opens.grothendieckTopology`
exactly when every point of `U` lies in some open `V` with an arrow `V ⟶ U` (i.e. `V ≤ U`)
belonging to
`S`. From such a covering sieve we extract a genuine open cover indexed by the arrows of `S`: the
index
type is `Σ V, {f : V ⟶ U // S f}`, the cover sends such a datum to its source `V`, and `hle` is `V
≤ U`.
The supremum equals `U` because: each member is `≤ U` (so `⨆ ≤ U`), and conversely every point of
`U`
is in some member by the covering property (so `U ≤ ⨆`); conclude by `le_antisymm`.
-/
@[sga "4½ Arcata 1.1" "necessary direction", sga "4½ Arcata 1.6.4" "partial"]
lemma exists_opens_cover_of_mem_grothendieckTopology
    (U : Opens X) (S : Sieve U) (hS : S ∈ Opens.grothendieckTopology X U) :
    ∃ (I : Type u) (cover : I → Opens X) (hle : ∀ i, cover i ≤ U)
      (_ : ∀ i, S.arrows (homOfLE (hle i))),
      (⨆ i, cover i) = U := by
  refine ⟨Σ V : Opens X, {f : V ⟶ U // S.arrows f},
    fun i => i.1, fun i => leOfHom i.2.1, fun i => ?_, ?_⟩
  · -- need S.arrows (homOfLE (leOfHom i.2.1)) ; homOfLE (leOfHom f) = f by subsingleton
    have : homOfLE (leOfHom i.2.1) = i.2.1 := Subsingleton.elim _ _
    rw [this]
    exact i.2.2
  · -- supremum = U
    refine le_antisymm (iSup_le fun i => leOfHom i.2.1) fun x hx => ?_
    obtain ⟨V, f, hf, hxV⟩ := hS x hx
    exact Opens.mem_iSup.2 ⟨⟨V, f, hf⟩, hxV⟩

/- **`toSheaf` of an injective resolution is exact in positive degree (as sheaves of abelian
groups).**
The forgetful functor `SheafOfModules.toSheaf R : Mod(O_X) ⥤ Sheaf(Ab)` is exact (it is the
composite
of forgetting module structure and the inclusion into presheaves, reflecting/forgetting along exact
functors; in particular it preserves exactness of short complexes). An injective resolution `I` of
`F`
has `I.cocomplex` exact at every degree `k + 1` (`InjectiveResolution.cocomplex_exactAt_succ`).
Applying
the exact functor `toSheaf R` degreewise preserves this exactness, so the complex of sheaves of
abelian
groups `(toSheaf R).mapHomologicalComplex |>.obj I.cocomplex` is exact at degree `k + 1`.
-/

/-- **Sheafification `presheafToSheaf` preserves finite colimits (clean).**
`presheafToSheaf J Ab` is the left adjoint of `sheafificationAdjunction`, hence preserves all
colimits;
this is recorded here as a clean (`sorryAx`-free) instance via `leftAdjoint_preservesColimits`,
which
takes priority over any stubbed colimit-preservation instance in scope. -/
noncomputable instance presheafToSheafPFC :
    Limits.PreservesFiniteColimits
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat) :=
  ⟨fun _ _ _ =>
    ((sheafificationAdjunction (Opens.grothendieckTopology X)
      AddCommGrpCat).leftAdjoint_preservesColimits).preservesColimitsOfShape⟩

/-- **Diagram-shifting transfer for colimit preservation.**
If `G` preserves the colimit of `E` and `G ⋙ F` preserves the colimit of `E`, then `F` preserves
the colimit of `E ⋙ G`. (The colimit cocone of `E ⋙ G` is `G.mapCocone (colimit.cocone E)`, a
colimit since `G` preserves it; `F` maps it to `(G ⋙ F).mapCocone (colimit.cocone E)`, a colimit
since `G ⋙ F` preserves it.) -/
theorem preservesColim_comp_transfer {A B Dc : Type _} [Category A] [Category B] [Category Dc]
    {K : Type _} [Category K] (E : K ⥤ A) (G : A ⥤ B) (F : B ⥤ Dc)
    (hG : Limits.PreservesColimit E G) (hGF : Limits.PreservesColimit E (G ⋙ F))
    (hE : Limits.HasColimit E) :
    Limits.PreservesColimit (E ⋙ G) F :=
  Limits.preservesColimit_of_preserves_colimit_cocone
    (Limits.isColimitOfPreserves G (Limits.colimit.isColimit E))
    (Limits.isColimitOfPreserves (G ⋙ F) (Limits.colimit.isColimit E))

/-- **`SheafOfModules.toSheaf R` preserves finite colimits.**
Both `SheafOfModules R` and `Sheaf J Ab` compute colimits by sheafifying the underlying presheaf
colimit, and `toSheaf` commutes with this. Concretely, write
`Lsh = PresheafOfModules.sheafification` (a left adjoint, hence preserves all colimits) and
`Gsh = forget R ⋙ restrictScalars`. The counit of `PresheafOfModules.sheafificationAdjunction` is
an isomorphism, so `Gsh ⋙ Lsh ≅ 𝟭`. Moreover
`Lsh ⋙ toSheaf R ≅ toPresheaf R.obj ⋙ presheafToSheaf J Ab` (`sheafificationCompToSheaf`), and the
right-hand composite preserves finite colimits because `toPresheaf` does and `presheafToSheaf` does
(as the left adjoint of `sheafificationAdjunction`). Given a finite diagram `D`, the transfer lemma
applied to `E := D ⋙ Gsh`, `G := Lsh`, `F := toSheaf R` shows `toSheaf R` preserves the colimit of
`(D ⋙ Gsh) ⋙ Lsh ≅ D`. -/
noncomputable instance toSheafPFC : Limits.PreservesFiniteColimits (SheafOfModules.toSheaf R) := by
  refine ⟨fun K _ _ => ?_⟩
  set Lsh : PresheafOfModules R.obj ⥤ SheafOfModules R :=
    PresheafOfModules.sheafification (𝟙 R.obj)
  set Gsh : SheafOfModules R ⥤ PresheafOfModules R.obj :=
    SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  -- `Lsh` preserves colimits of shape `K` (it is a left adjoint).
  have lshPres : Limits.PreservesColimitsOfShape K Lsh :=
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 R.obj)).leftAdjoint_preservesColimits).preservesColimitsOfShape
  -- `Lsh ⋙ toSheaf R` preserves colimits of shape `K`, built from clean pieces.
  have compPres : Limits.PreservesColimitsOfShape K (Lsh ⋙ SheafOfModules.toSheaf R) := by
    have hiso : Lsh ⋙ SheafOfModules.toSheaf R ≅
        PresheafOfModules.toPresheaf R.obj ⋙
          presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat :=
      PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)
    have hcleanToP : Limits.PreservesColimitsOfShape K (PresheafOfModules.toPresheaf R.obj) :=
      (inferInstance : Limits.PreservesFiniteColimits
        (PresheafOfModules.toPresheaf R.obj)).preservesFiniteColimits K
    have hcleanPTS : Limits.PreservesColimitsOfShape K
        (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat) :=
      ((sheafificationAdjunction (Opens.grothendieckTopology X)
        AddCommGrpCat).leftAdjoint_preservesColimits).preservesColimitsOfShape
    have hcomp : Limits.PreservesColimitsOfShape K
        (PresheafOfModules.toPresheaf R.obj ⋙
          presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat) :=
      Limits.comp_preservesColimitsOfShape _ _
    exact Limits.preservesColimitsOfShape_of_natIso hiso.symm
  -- The counit of the sheafification adjunction is an isomorphism: `Gsh ⋙ Lsh ≅ 𝟭`.
  have counitIso : Gsh ⋙ Lsh ≅ 𝟭 (SheafOfModules R) :=
    asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit
  refine ⟨fun {D} => ?_⟩
  have key : Limits.PreservesColimit ((D ⋙ Gsh) ⋙ Lsh) (SheafOfModules.toSheaf R) :=
    preservesColim_comp_transfer (D ⋙ Gsh) Lsh (SheafOfModules.toSheaf R)
      (lshPres.preservesColimit) (compPres.preservesColimit) inferInstance
  have hdiso : (D ⋙ Gsh) ⋙ Lsh ≅ D :=
    (Functor.associator D Gsh Lsh) ≪≫ Functor.isoWhiskerLeft D counitIso ≪≫ D.rightUnitor
  exact Limits.preservesColimit_of_iso_diagram (SheafOfModules.toSheaf R) hdiso

omit [EnoughInjectives (SheafOfModules R)] in
/-- Applying `SheafOfModules.toSheaf R` to an injective resolution of `F` gives a cocomplex of
abelian-group sheaves that is exact in every positive degree. -/
lemma toSheaf_cocomplex_exactAt
    (F : SheafOfModules R) (I : InjectiveResolution F) (k : ℕ) :
    (((SheafOfModules.toSheaf R).mapHomologicalComplex _).obj I.cocomplex).ExactAt (k + 1) := by
  rw [HomologicalComplex.exactAt_iff]
  exact ((HomologicalComplex.exactAt_iff _ _).1 (I.cocomplex_exactAt_succ k)).map
    (SheafOfModules.toSheaf R)

/-- **Cycles comparison isomorphism, needing only kernel preservation.**
For a short complex `S` and a functor `F` preserving the kernel `parallelPair S.g 0`, the cycles of
the mapped complex are isomorphic to `F` applied to the cycles. Unlike `ShortComplex.mapCyclesIso`,
this only needs `PreservesLimit (parallelPair S.g 0) F` (cycles is a kernel), not the full
`PreservesLeftHomologyOf` (which would also require preserving a cokernel). Built from
`cyclesIsoKernel` and `PreservesKernel.iso`. -/
noncomputable def mapCyclesIsoClean {C D : Type _} [Category C] [Category D] [Abelian C] [Abelian D]
    (S : ShortComplex C) (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [Limits.PreservesLimit (Limits.parallelPair S.g 0) F] :
    (S.map F).cycles ≅ F.obj S.cycles :=
  (S.map F).cyclesIsoKernel ≪≫ (Limits.PreservesKernel.iso F S.g).symm ≪≫
    (F.mapIso S.cyclesIsoKernel).symm

/-- Compatibility of `mapCyclesIsoClean` with `iCycles`: it intertwines the cycle inclusions. -/
lemma mapCyclesIsoClean_hom_iCycles {C D : Type _} [Category C] [Category D] [Abelian C] [Abelian D]
    (S : ShortComplex C) (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [Limits.PreservesLimit (Limits.parallelPair S.g 0) F] :
    (mapCyclesIsoClean S F).hom ≫ F.map S.iCycles = (S.map F).iCycles := by
  have hRHS : (S.map F).iCycles
      = (S.map F).cyclesIsoKernel.hom ≫ Limits.kernel.ι ((S.map F).g) := by
    rw [(S.map F).cyclesIsoKernel_hom, Limits.kernel.lift_ι]
  rw [hRHS]
  unfold mapCyclesIsoClean
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Category.assoc]
  rw [← F.map_comp]
  rw [show S.cyclesIsoKernel.inv ≫ S.iCycles = Limits.kernel.ι S.g from by
    rw [S.cyclesIsoKernel_inv]; simp [ShortComplex.liftCycles_i]]
  congr 1
  rw [Iso.inv_comp_eq, Limits.PreservesKernel.iso_hom]
  exact (Limits.kernelComparison_comp_ι S.g F).symm

omit [EnoughInjectives (SheafOfModules R)] in
/-- **Core local-vanishing lemma (positive degree), at the level of the section complexes.**
Fix an injective resolution `I` of `F`. Let `n > 0`, `U` an open, and let `ξ` be a degree-`n`
homology class of the section complex `secCx R I U = Γ(U, I^•)`. Then there is an open cover
`U = ⨆ i, cover i` (with `cover i ≤ U`) such that for every `i` the restriction-induced map on
homology, `HomologicalComplex.homologyMap (Γ(cover i, -) restriction of I^•) n`, sends `ξ` to `0`.

Rigorous argument.
1. The class `ξ ∈ H^n(Γ(U, I^•))` is represented by a cocycle: `homologyπ` is an epimorphism, and
   `AddCommGrpCat` is a concrete (in fact `forget`-faithful, surjective-on-epi) category, so there
   is
   an actual section `z ∈ Γ(U, I^n)` with `d^n z = 0` whose homology class is `ξ`. (Mathlib:
   `HomologicalComplex.homologyπ` epi + `ShortComplex`/`AddCommGrp` concreteness; `liftCycles`
   packages
   `z` as a cycle.)
2. Apply `toSheaf` to `I`: by `toSheaf_cocomplex_exactAt`, the complex of sheaves of abelian groups
   `toSheaf(I^•)` is exact at degree `n` (here `n = k+1 > 0`). Exactness at `n` means the canonical
   map
   `toSheaf(I^{n-1}) → ker(d^n)` (equivalently `toSheaf(I^{n-1}) → cycles_n`) is an epimorphism of
   sheaves (`ShortComplex.exact_iff_epi_toCycles` / `Exact.epi_kernelLift`).
3. An epimorphism of sheaves of abelian groups is locally surjective
   (`Sheaf.isLocallySurjective_iff_epi'`, using `HasSheafify` + balancedness of the abelian sheaf
   category). Hence the section `z`, viewed as a section of `ker(d^n)` over `U`, is locally in the
   image
   of `d^{n-1}`: the image sieve `Presheaf.imageSieve (d^{n-1}) z` is a covering sieve of `U`
   (`Presheaf.imageSieve_mem`).
4. By `exists_opens_cover_of_mem_grothendieckTopology`, this covering sieve yields an open cover
   `U = ⨆ i, cover i` with each `cover i ≤ U` and, for each `i`, an arrow in the sieve — i.e. a
   section
   `w_i ∈ Γ(cover i, I^{n-1})` with `d^{n-1} w_i = z|_{cover i}` (`Presheaf.localPreimage` /
   `app_localPreimage`).
5. Fix `i`, write `h_i : cover i ≤ U`. The restriction chain map `r_i : secCx R I U ⟶ secCx R I
(cover i)`
   is `(NatTrans.mapHomologicalComplex (secRestrict R h_i) _).app I.cocomplex`; on degree-`m`
   sections it
   is the sheaf restriction `Γ(U, I^m) → Γ(cover i, I^m)`. Naturality of `homologyMap`/`cyclesMap`
   (`HomologicalComplex.homologyπ_naturality`, `liftCycles_comp_cyclesMap`) shows that `homologyMap
   r_i n`
   sends the class of `z` to the class of `z|_{cover i}`. But `z|_{cover i} = d^{n-1} w_i` is a
   coboundary,
   so by `HomologicalComplex.liftCycles_homologyπ_eq_zero_of_boundary` its homology class is `0`.
   Hence
   `homologyMap r_i n ξ = 0`.
-/
@[sga "4 V 3.1" "special case"]
lemma exists_cover_homologyMap_eq_zero
    (F : SheafOfModules R) (U : Opens X) (n : ℕ) (hn : 0 < n)
    (I : InjectiveResolution F) (ξ : (secCx R I U).homology n) :
    ∃ (J : Type u) (cover : J → Opens X) (hle : ∀ i, cover i ≤ U),
      ((⨆ i, cover i) = U) ∧
      ∀ i, (HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex (secRestrict R (hle i)) _).app I.cocomplex) n) ξ = 0 := by
  classical
  -- Local evaluation-at-an-open functor on abelian-group sheaves, and the toSheaf complex.
  let evalU : Opens X → (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat ⥤ AddCommGrpCat) :=
    fun W => (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj (op W)
  -- `evalU W` preserves finite limits (it is `sheafToPresheaf ⋙ evaluation`).
  have evalU_pfl : ∀ W : Opens X, Limits.PreservesFiniteLimits (evalU W) := by
    intro W
    change Limits.PreservesFiniteLimits
      ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj (op W))
    have h : (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj (op W)
        = sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat
          ⋙ (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op W) := rfl
    rw [h]; infer_instance
  -- The complex of sheaves of abelian groups `toSheaf(I^•)` and its degree-`n` short complex.
  set S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) :=
    (((SheafOfModules.toSheaf R).mapHomologicalComplex _).obj I.cocomplex).sc n with hS
  -- Step 1: lift `ξ` to a cycle `ctilde`.
  obtain ⟨ctilde, hctilde⟩ :=
    (AddCommGrpCat.epi_iff_surjective ((secCx R I U).homologyπ n)).mp inferInstance ξ
  -- Step 2–3: `S.toCycles` is epi (exactness), so locally surjective; its image sieve covers `U`.
  have hex : S.Exact := by
    rw [hS, ← HomologicalComplex.exactAt_iff]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    exact toSheaf_cocomplex_exactAt R F I k
  have hls : Sheaf.IsLocallySurjective S.toCycles :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat S.toCycles).mpr hex.epi_toCycles
  have hpls : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) S.toCycles.hom := hls
  -- The section `z'` of `S.cycles` over `U` representing `ctilde`.
  set z' : (evalU U).obj S.cycles := (mapCyclesIsoClean S (evalU U)).hom ctilde with hz'
  have hmem : Presheaf.imageSieve S.toCycles.hom z' ∈ Opens.grothendieckTopology X U :=
    Presheaf.imageSieve_mem (Opens.grothendieckTopology X) S.toCycles.hom (U := op U) z'
  -- Step 4: extract an open cover from the covering image sieve.
  obtain ⟨J, cover, hle, harrow, hsup⟩ :=
    exists_opens_cover_of_mem_grothendieckTopology U (Presheaf.imageSieve S.toCycles.hom z') hmem
  refine ⟨J, cover, hle, hsup, fun i => ?_⟩
  -- Step 5: fix `i`. The local preimage `w` of `z'` over `cover i`.
  set V := cover i
  set hVle := hle i
  set w : (evalU V).obj S.X₁ :=
    Presheaf.localPreimage S.toCycles.hom z' (homOfLE hVle) (harrow i)
  -- The key cycle identity: `iCycles` of `z'` (over `U`) is `iCycles ctilde`.
  have hkey : (evalU U).map S.iCycles z' = (secCx R I U).iCycles n ctilde := by
    rw [hz', ← CategoryTheory.ConcreteCategory.comp_apply,
      mapCyclesIsoClean_hom_iCycles S (evalU U)]
    rfl
  -- The boundary identity `hbnd : iCycles_V (cyclesMap r ctilde) = d^{prev n, n} w`.
  set r := (NatTrans.mapHomologicalComplex (secRestrict R hVle) _).app I.cocomplex
  have hbnd : (secCx R I V).iCycles n (HomologicalComplex.cyclesMap r n ctilde)
      = (secCx R I V).d ((ComplexShape.up ℕ).prev n) n w := by
    -- LHS = (r.f n)(iCycles ctilde)
    have hL : (secCx R I V).iCycles n (HomologicalComplex.cyclesMap r n ctilde)
        = (r.f n) ((secCx R I U).iCycles n ctilde) := by
      rw [← CategoryTheory.ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i,
        CategoryTheory.ConcreteCategory.comp_apply]
    rw [hL, ← hkey]
    have happ := Presheaf.app_localPreimage S.toCycles.hom z' (homOfLE hVle) (harrow i)
    have hcongr := congrArg (CategoryTheory.ConcreteCategory.hom (S.iCycles.hom.app (op V))) happ
    rw [← CategoryTheory.ConcreteCategory.comp_apply] at hcongr
    have hnatu : S.cycles.obj.map (homOfLE hVle).op ≫ S.iCycles.hom.app (op V)
        = S.iCycles.hom.app (op U) ≫ S.X₂.obj.map (homOfLE hVle).op :=
      (S.iCycles.hom.naturality (homOfLE hVle).op)
    rw [show S.toCycles.hom.app (op V) ≫ S.iCycles.hom.app (op V)
        = S.f.hom.app (op V) from by
          rw [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom,
            S.toCycles_i]] at hcongr
    rw [← CategoryTheory.ConcreteCategory.comp_apply (f := S.cycles.obj.map (homOfLE hVle).op),
      hnatu, CategoryTheory.ConcreteCategory.comp_apply] at hcongr
    -- hcongr : S.f.hom.app(op V) w = S.X₂.obj.map g (S.iCycles.hom.app(op U) z')
    exact hcongr.symm
  -- Finish: combine `hbnd` with the homology-π naturality + boundary vanishing.
  have hnat := HomologicalComplex.homologyπ_naturality r n
  rw [← hctilde, ← CategoryTheory.ConcreteCategory.comp_apply, hnat,
    CategoryTheory.ConcreteCategory.comp_apply]
  have htc : (secCx R I V).iCycles n
        ((secCx R I V).toCycles ((ComplexShape.up ℕ).prev n) n w)
      = (secCx R I V).d ((ComplexShape.up ℕ).prev n) n w := by
    rw [← CategoryTheory.ConcreteCategory.comp_apply, (secCx R I V).toCycles_i]
  have hmono : Function.Injective ((secCx R I V).iCycles n) := by
    rw [← AddCommGrpCat.mono_iff_injective]; infer_instance
  have heq : HomologicalComplex.cyclesMap r n ctilde
      = (secCx R I V).toCycles ((ComplexShape.up ℕ).prev n) n w :=
    hmono (hbnd.trans htc.symm)
  rw [heq, ← CategoryTheory.ConcreteCategory.comp_apply, (secCx R I V).toCycles_comp_homologyπ]
  rfl

-- Main Statement(s)

/-- **Stacks Project Tag 01E3 (Lemma 20.7.2), Locality of cohomology.**
For a ringed space with structure sheaf `R`, a sheaf of `O_X`-modules `F`, an open `U`, a positive
degree `n`, and a cohomology class `ξ ∈ H^n(U, F)`, there exists an open covering
`U = ⨆ i, cover i` (each `cover i ⊆ U`) on which `ξ` restricts to `0`.

Rigorous argument (assembly).
Choose the canonical injective resolution `I := InjectiveResolution.of F` of `F`. The iso
`e_W : Hgroup R W n F ≅ (secCx R I W).homology n` from `InjectiveResolution.isoRightDerivedObj`
identifies cohomology with section-complex homology, naturally in the open `W` in the following
precise
sense (`InjectiveResolution.rightDerived_app_eq`): for `h : V ≤ U`,
`Hrestrict R h n F = e_U.hom ≫ homologyMap (r_V) n ≫ e_V.inv`, where
`r_V = (NatTrans.mapHomologicalComplex (secRestrict R h) _).app I.cocomplex`.

Transport `ξ` to `ξ' := e_U.hom ξ ∈ (secCx R I U).homology n`. Apply
`exists_cover_homologyMap_eq_zero`
to `ξ'` (using `n > 0`) to get a cover `U = ⨆ i, cover i`, `hle i : cover i ≤ U`, with
`homologyMap (r_{cover i}) n ξ' = 0` for each `i`. Then, for each `i`,
`Hrestrict R (hle i) n F ξ = e_{cover i}.inv (homologyMap (r_{cover i}) n (e_U.hom ξ))
  = e_{cover i}.inv (homologyMap (r_{cover i}) n ξ') = e_{cover i}.inv 0 = 0`,
using that `e_{cover i}.inv` is an additive group hom (sends `0` to `0`). This is the required
cover. -/
@[stacks 01E3, sga "4 V 3.1" "special case"]
theorem locality_of_cohomology
    (F : SheafOfModules R) (U : Opens X) (n : ℕ) (hn : 0 < n)
    (ξ : Hgroup R U n F) :
    ∃ (I : Type u) (cover : I → Opens X) (hle : ∀ i, cover i ≤ U),
      ((⨆ i, cover i) = U) ∧
      ∀ i, Hrestrict R (hle i) n F ξ = 0 := by
  -- Fix the canonical injective resolution of `F`.
  set Ires : InjectiveResolution F := InjectiveResolution.of F
  -- The comparison iso `Hgroup R W n F ≅ (secCx R Ires W).homology n` is
  -- `Ires.isoRightDerivedObj (secF R W) n` (from `InjectiveResolution.isoRightDerivedObj`).
  -- Transport `ξ` to the section-complex homology class over `U` and apply the core lemma.
  obtain ⟨J, cover, hle, hsup, hzero⟩ :=
    exists_cover_homologyMap_eq_zero R F U n hn Ires
      ((Ires.isoRightDerivedObj (secF R U) n).hom ξ)
  refine ⟨J, cover, hle, hsup, fun i => ?_⟩
  -- Convert `Hrestrict ... ξ = 0` to the section-complex statement via `rightDerived_app_eq`,
  -- then use `hzero i`. The naturality square is `Hrestrict = e_U.hom ≫ homologyMap r ≫ e_{cover
  -- i}.inv`.
  -- After substituting, `Hrestrict ... ξ = e_{cover i}.inv (homologyMap r n (e_U.hom ξ)) =
  -- e_{cover i}.inv 0 = 0`.
  have hkey : Hrestrict R (hle i) n F
      = (Ires.isoRightDerivedObj (secF R U) n).hom
          ≫ (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) n).map
            ((NatTrans.mapHomologicalComplex (secRestrict R (hle i)) _).app Ires.cocomplex)
          ≫ (Ires.isoRightDerivedObj (secF R (cover i)) n).inv :=
    InjectiveResolution.rightDerived_app_eq (secRestrict R (hle i)) Ires n
  -- Apply both sides to `ξ`. The composite, applied to `ξ`, is
  -- `e_{cover i}.inv (homologyMap (...) n (e_U.hom ξ))`. By `hzero i` the inner value is `0`,
  -- and `e_{cover i}.inv` (an `AddCommGrpCat` hom) sends `0 ↦ 0` (`map_zero`).
  rw [hkey]
  rw [show (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) n).map
        ((NatTrans.mapHomologicalComplex (secRestrict R (hle i)) _).app Ires.cocomplex)
      = HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex (secRestrict R (hle i)) _).app Ires.cocomplex) n
            from rfl]
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  -- Goal is now `e_{cover i}.inv (homologyMap (...) n (e_U.hom ξ)) = 0`, and `hzero i` is exactly
  -- `homologyMap (...) n (e_U.hom ξ) = 0` (definitionally; the two `homologyMap` terms are defeq).
  -- Close by congruence on the outer hom + `map_zero` (uses defeq rather than syntactic match).
  exact (congrArg (ConcreteCategory.hom (Ires.isoRightDerivedObj (secF R (cover i)) n).inv)
    (hzero i)).trans (map_zero _)
