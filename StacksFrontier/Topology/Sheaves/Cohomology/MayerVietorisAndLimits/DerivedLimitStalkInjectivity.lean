module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGESuccTriangle
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncationTower
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.StalkwiseIsomorphism
public import StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelian
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MonoHomologyProjection
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
public import StacksFrontier.Homology.Injectives.DerivedCategory.ProductsAndCoproducts
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CohomologyPresheafSheafification
public import StacksFrontier.CategoryTheory.Functor.NatIsoMonoEpi
import StacksCore.Tactic.StacksAttribute

/-!
# Derived limits of inverse systems in the derived category of a ringed space

Let `(X, 𝒪_X)` be a ringed space. Two statements about derived limits in `D(𝒪_X)` are proved
here, the second from the first.

The local criterion. Let `(Kₙ)` be an inverse system in `D(𝒪_X)` and let `L` be a derived limit
of it, presented by its defining distinguished triangle. Fix a point `x`, a degree `m`, an index
`n₀` and a fundamental system `𝔘` of open neighbourhoods of `x`. If over every `U ∈ 𝔘` the first
derived inverse limit of the tower `Hᵐ⁻¹(U, Kₙ)` vanishes and the transition maps
`Hᵐ(U, Kₙ) ⟶ Hᵐ(U, K_{n₀})` are injective for `n ≥ n₀`, then

`Hᵐ(R lim Kₙ)ₓ ⟶ Hᵐ(K_{n₀})ₓ`

is injective.

The argument is the one of the source. Over a single `U ∈ 𝔘` the vanishing of `R¹ lim` in degree
`m - 1` makes the difference map of the tower surjective on sections, so the long exact sequence
of the derived-limit triangle makes `Hᵐ(U, L)` inject into the product, hence into the limit of
the tower, whose projection to the stage `n₀` is injective because every transition map above
`n₀` is. That gives injectivity of the map of cohomology *presheaves* over every `U ∈ 𝔘`, and the
stalk at `x` is the filtered colimit of these sections over `𝔘`, so injectivity passes to the
stalk; sheafification does not change stalks, and the sheafified cohomology presheaf is the
cohomology sheaf by Tag 0BKJ.

The convergence statement. Let `E` be an object of `D(𝒪_X)` and suppose every point `x` carries
a function `p(x, -) : ℤ → ℤ` and a fundamental system `𝔘ₓ` of open neighbourhoods of `x` with
`Hᵖ(U, H^{m-p}(E)) = 0` whenever `U ∈ 𝔘ₓ` and `p > p(x, m)`. Then the canonical map

`E ⟶ R lim τ_{≥ -n} E`

is an isomorphism in `D(𝒪_X)`. Fixing `m`, the map `E ⟶ τ_{≥ -n} E` is already invertible on `Hᵐ`
for `n ≥ -m`, so it suffices to exhibit, at each point `x`, a stage `n(x) ≥ -m` at which
`Hᵐ(R lim τ_{≥ -n} E)ₓ ⟶ Hᵐ(τ_{≥ -n(x)} E)ₓ` is injective: the composite through it is then
bijective, and invertibility of a map of `D(𝒪_X)` is tested on the stalks of its cohomology
sheaves. Injectivity at the stage
`n(x) = 1 + max {-m, p(x, m-1) - m, -1 + p(x, m) - m, -2 + p(x, m+1) - m}`
comes from the local criterion above: the triangles
`H^{-n-1}(E)[n+1] ⟶ τ_{≥ -(n+1)} E ⟶ τ_{≥ -n} E` of Tag 08J5 reduce its two hypotheses to the
vanishing of `H^{m+n}`, `H^{m+n+1}` and `H^{m+n+2}` of `U` with coefficients in `H^{-n-1}(E)`,
which is what the choice of `n(x)` extracts from the standing hypothesis.

A global form of the hypothesis suffices: if a single function `p(-) : ℤ → ℤ` and a single set `B`
of opens of `X` are such that every open of `X` is a union of members of `B` and
`Hᵖ(U, H^{m-p}(E)) = 0` for `U ∈ B` and `p > p(m)`, then the convergence statement applies at
every point, because the members of `B` containing a given point `x` form a fundamental system of
open neighbourhoods of `x`.

## Main results

All of them live in the namespace `Stacks.Cohomology.DerivedLimitStalk`.

* `mono_stalkFunctor_map_of_nhds_basis`: a map of presheaves of abelian groups which is injective
  on sections over a fundamental system of neighbourhoods of a point is injective on the stalk
  there.
* `cohomology_derivedLimit_projection_mono_on_stalk` (Tag 0D61): the injectivity criterion on the
  stalk.
* `isIso_to_isDerivedLimit_truncGETower_of_local_vanishing` (Tag 0D62): the convergence
  statement.
* `isIso_to_isDerivedLimit_truncGETower_of_vanishing_on_cover` (Tag 08U2): the convergence
  statement from a single function `p(-)` and a single set of opens covering every open of `X`.
* `exists_presented_derivedLimit_truncGETower`: for every ringed space and every `E`, the
  truncation tower has a presented derived limit together with the canonical map of Remark 0H72
  into it, with no hypothesis whatsoever.
* `exists_isIso_to_derivedLimit_truncGETower_of_vanishing_on_cover` (Tag 08U2): the same
  convergence statement with that derived limit and that canonical map constructed rather than
  quantified over, which is the shape in which the source states it.
* `exists_and_forall_isIso_to_derivedLimit_truncGETower_of_local_vanishing` (Tag 0D62) and
  `exists_and_forall_isIso_to_derivedLimit_truncGETower_of_vanishing_on_cover` (Tag 08U2): the
  derived limit of the truncation tower exists with its canonical map, and every such canonical
  map is an isomorphism.

## Implementation notes

The cohomology groups `Hᵐ(U, Kₙ)` are the sections over `U` of the derived cohomology presheaf of
Tag 0BKJ, so their transition maps are canonically induced by those of the tower; Tag 0BKJ's
`cohomologyPresheafEvaluationIso` identifies them with derived cohomology over `U`. The first
derived inverse limit is the cokernel of the usual `1 - shift` endomorphism of the product. The
derived limit is presented by the distinguished product triangle rather than by a predicate, so
the component of the structural map at any index is literally the canonical projection.

The fundamental system of open neighbourhoods is a `Filter.HasBasis` for `nhds x` indexed by a set
of opens; this is the formulation under which the stalk, a colimit over all open neighbourhoods,
is computed by the subsystem.

The only instance arguments the statements below carry are the two `HasDerivedCategory` ones, and
those are genuine generality: nothing here needs a particular model of `D(𝒪_X)`. In particular no
`HasRightDerivedFunctor` precondition is carried. Sheaves of `𝒪_X`-modules are Grothendieck
abelian, so every functor out of their homotopy category has a total right derived functor, and
instance search therefore supplies on its own the instance under which a statement may name
`derivedSectionsPresheaf`; it is proved with nothing assumed by
`Stacks.Cohomology.OpenSubspace.hasRightDerivedFunctor_of_moduleKInjectives`, and the instance
search finds is `Stacks.Cohomology.Localization.hasRightDerivedFunctorOfGrothendieck`. The numbered
hypotheses `hlimOne` and `hinj` of Tag 0D61 are, by contrast, the source's own two assumptions and
stay; `isIso_to_isDerivedLimit_truncGETower_of_local_vanishing` below shows them being discharged
rather than assumed, from the local vanishing hypothesis of Tag 0D62.

In the convergence statement the vanishing hypothesis quantifies only over natural numbers `p`,
since cohomology in negative degrees vanishes anyway; this makes the hypothesis weaker than the
source's and so the statement stronger. The truncation tower is
`Stacks.DerivedLimit.truncGETower`, and its derived limit is again supplied by the defining
distinguished triangle together with a map `c` all of whose composites with the projections of
that triangle are the canonical truncation maps `DerivedCategory.TStructure.t.truncGEπ`. This
pins `c` to the canonical map of Derived Categories, Remark 0H72, rather than to an arbitrary map
to an arbitrary derived limit, which the predicate `IsDerivedLimit` alone would not do, since it
does not remember the first arrow of its triangle.

## References

* [Stacks Project, Tag 0D61](https://stacks.math.columbia.edu/tag/0D61)
* [Stacks Project, Tag 0D62](https://stacks.math.columbia.edu/tag/0D62)
* [Stacks Project, Tag 0BKJ](https://stacks.math.columbia.edu/tag/0BKJ)
* [Stacks Project, Tag 08J5](https://stacks.math.columbia.edu/tag/08J5)
* [Stacks Project, Tag 08U1](https://stacks.math.columbia.edu/tag/08U1)
* [Stacks Project, Tag 08U2](https://stacks.math.columbia.edu/tag/08U2)
* [Stacks Project, Tag 0H72](https://stacks.math.columbia.edu/tag/0H72)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open Stacks.Cohomology.CohomologyPresheaf

universe wX wP u

namespace Stacks.Cohomology.DerivedLimitStalk

/-! ### Injectivity on a stalk from injectivity on a fundamental system of neighbourhoods -/

/-- A map of presheaves of abelian groups on a topological space which is injective on sections
over every member of a fundamental system of open neighbourhoods of a point is injective on the
stalk at that point: the stalk is the filtered colimit of the sections over all neighbourhoods,
and the given system is cofinal in it. -/
public theorem mono_stalkFunctor_map_of_nhds_basis {X : TopCat.{u}} (x : X)
    (𝔘 : Set (Opens X))
    (hbasis : (nhds x).HasBasis (fun U : Opens X ↦ U ∈ 𝔘) (fun U ↦ (U : Set X)))
    {F G : X.Presheaf AddCommGrpCat.{u}} (f : F ⟶ G)
    (hmono : ∀ U ∈ 𝔘, Mono (f.app (Opposite.op U))) :
    Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f) := by
  classical
  refine (AddCommGrpCat.mono_iff_injective _).2 ?_
  let restrict := (Functor.whiskeringLeft (OpenNhds x)ᵒᵖ (Opens X)ᵒᵖ
    AddCommGrpCat.{u}).obj (OpenNhds.inclusion x).op
  let D := restrict.obj F
  let E := restrict.obj G
  intro a b hab
  obtain ⟨j, s, t, rfl, rfl⟩ :=
    Types.FilteredColimit.jointly_surjective_of_isColimit₂
      (isColimitOfPreserves (forget AddCommGrpCat.{u}) (colimit.isColimit D)) a b
  have hmap : colimit.ι D j ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f =
      f.app (Opposite.op j.unop.1) ≫ colimit.ι E j := by
    change colimit.ι D j ≫ colim.map (restrict.map f) =
      (restrict.map f).app j ≫ colimit.ι E j
    exact colimit.ι_map (restrict.map f) j
  have hG : (colimit.ι E j) ((f.app (Opposite.op j.unop.1)) s) =
      (colimit.ι E j) ((f.app (Opposite.op j.unop.1)) t) := by
    change ((colimit.ι D j ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f) s) =
      ((colimit.ι D j ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f) t) at hab
    rw [hmap] at hab
    convert hab using 1 <;> rfl
  obtain ⟨k, g, heq⟩ :=
    ((colimit.isColimit E).eq_iff' ((f.app (Opposite.op j.unop.1)) s)
      ((f.app (Opposite.op j.unop.1)) t)).mp hG
  let W : Opens X := k.unop.1
  have hxW : x ∈ W := k.unop.2
  obtain ⟨V, hV𝔘, hVW⟩ := hbasis.mem_iff.mp (W.2.mem_nhds hxW)
  have hxV : x ∈ V := mem_of_mem_nhds (hbasis.mem_of_mem hV𝔘)
  let g' : (⟨V, hxV⟩ : OpenNhds x) ⟶ ⟨W, hxW⟩ := homOfLE hVW
  let α := restrict.map f
  let jV : (OpenNhds x)ᵒᵖ := Opposite.op ⟨V, hxV⟩
  let gV : j ⟶ jV := g ≫ g'.op
  have heqV : D.map gV s = D.map gV t := by
    have heqV' : E.map gV (α.app j s) = E.map gV (α.app j t) := by
      change (E.map (g ≫ g'.op)) (α.app j s) = (E.map (g ≫ g'.op)) (α.app j t)
      rw [E.map_comp g g'.op]
      convert congrArg (fun z ↦ E.map g'.op z) heq using 1 <;> rfl
    exact (AddCommGrpCat.mono_iff_injective _).1 (hmono V hV𝔘) (by
      convert (α.naturality_apply gV s).trans
        (heqV'.trans (α.naturality_apply gV t).symm) using 1 <;> rfl)
  exact ((colimit.isColimit D).eq_iff' s t).2 ⟨jV, gV, heqV⟩

/-- Sheafification does not change stalks, so a map of presheaves of abelian groups which is
injective on the stalk at a point stays injective there after sheafification. -/
private theorem mono_stalkFunctor_map_sheafifyMap {X : TopCat.{u}} (x : X)
    {F G : X.Presheaf AddCommGrpCat.{u}} (f : F ⟶ G)
    (hf : Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f)) :
    Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (CategoryTheory.sheafifyMap (Opens.grothendieckTopology X) f)) := by
  let S := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  let J := Opens.grothendieckTopology X
  have : IsIso (S.map (CategoryTheory.toSheafify J F)) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} F
  have : IsIso (S.map (CategoryTheory.toSheafify J G)) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} G
  have hnat := congrArg S.map (CategoryTheory.toSheafify_naturality J f)
  simp only [Functor.map_comp] at hnat
  rw [← mono_comp_iff_of_isIso (S.map (CategoryTheory.toSheafify J F)), ← hnat]
  exact @mono_comp _ _ _ _ _ _ hf _ (IsIso.mono_of_iso _)

/-! ### Tag 0D61 -/

/-- **Stacks Project, Tag 0D61.** A locally vanishing `R¹ lim` in degree `m - 1` and eventual
injectivity on cohomology in degree `m`, over a fundamental system of open neighbourhoods of `x`,
force the projection from a derived limit to the stage `n₀` to be injective on the stalk at `x`
of the degree-`m` cohomology sheaf.

Both numbered conditions of the source appear as binders, in the source's own position —
universally quantified over the members `U` of the fundamental system `𝔘`: `hlimOne` is
`R¹ lim Hᵐ⁻¹(U, Kₙ) = 0`, as the vanishing of the cokernel of the `1 - shift` endomorphism of the
product, and `hinj` is the injectivity of `Hᵐ(U, Kₙ) ⟶ Hᵐ(U, K_{n₀})` for `n ≥ n₀`. The source's
`n(x)` is `n₀` and its `𝔘ₓ` is `𝔘`, given here as arguments rather than existentially; the derived
limit `R lim Kₙ` is `L` together with `p` and `hL`, which say that `p` is the structural map of
the defining distinguished triangle, so `p ≫ Pi.π n₀` is the source's `R lim Kₙ ⟶ K_{n₀}` and not
an arbitrary map. -/
@[stacks 0D61]
public theorem cohomology_derivedLimit_projection_mono_on_stalk {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} O)]
    [HasDerivedCategory.{wP} (PresheafOfModules.{u} O.obj)]
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} O))
    (L : DerivedCategory (SheafOfModules.{u} O))
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hL : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (SheafOfModules.{u} O)))
    (x : X) (m : ℤ) (n₀ : ℕ) (𝔘 : Set (Opens X))
    (hbasis : (nhds x).HasBasis (fun U : Opens X ↦ U ∈ 𝔘) (fun U ↦ (U : Set X)))
    (hlimOne : ∀ U ∈ 𝔘,
      let F := K ⋙ derivedSectionsPresheaf O ⋙
        DerivedCategory.homologyFunctor (PresheafOfModules.{u} O.obj) (m - 1) ⋙
        PresheafOfModules.evaluation O.obj (Opposite.op U)
      IsZero (cokernel (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) (n + 1) ≫
            F.map (homOfLE (Nat.le_succ n)).op)))
    (hinj : ∀ U ∈ 𝔘,
      let F := K ⋙ derivedSectionsPresheaf O ⋙
        DerivedCategory.homologyFunctor (PresheafOfModules.{u} O.obj) m ⋙
        PresheafOfModules.evaluation O.obj (Opposite.op U)
      ∀ (n : ℕ) (hn : n₀ ≤ n), Mono (F.map (homOfLE hn).op)) :
    Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((SheafOfModules.forget O ⋙ PresheafOfModules.toPresheaf O.obj).map
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} O) m).map
          (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n₀)))) := by
  classical
  have : IsGrothendieckAbelian.{u} (SheafOfModules.{u} O) :=
    Stacks.SheafOfModules.sheafModulesGrothendieck _ O
  let P := PresheafOfModules.{u} O.obj
  let R := derivedSectionsPresheaf O
  let H := R ⋙ DerivedCategory.homologyFunctor P m
  let φ := p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n₀
  have : HasExactLimitsOfShape (Discrete ℕ) P :=
    HasExactLimitsOfShape.domain_of_functor (Discrete ℕ) (PresheafOfModules.toPresheaf O.obj)
  have := Stacks.DerivedProducts.hasProductsOfShape_nat (A := P)
  have (r : ℤ) : PreservesLimitsOfShape (Discrete ℕ)
      (DerivedCategory.homologyFunctor P r) :=
    Stacks.DerivedProducts.preservesLimitsOfShape_discrete_of_isIso_piComparison _
      fun Y ↦ Stacks.DerivedProducts.isIso_piComparison_homologyFunctor Y r
  have hmono : ∀ U ∈ 𝔘, Mono ((H.map φ).app (Opposite.op U)) := by
    intro U hU
    let E := PresheafOfModules.evaluation.{u} O.obj (Opposite.op U)
    obtain ⟨hProd, δ', hT'⟩ :=
      Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor (SheafOfModules.forget O) R
        ((homotopySectionsPresheaf O).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)))
        K L p hL
    have hProd' : HasProduct (fun n : ℕ ↦ (K ⋙ R).obj (⟨n⟩ : ℕᵒᵖ)) := hProd
    let T' := Triangle.mk (R.map p ≫ piComparison R (fun n : ℕ ↦ K.obj ⟨n⟩))
      (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ (K ⋙ R).obj (⟨n⟩ : ℕᵒᵖ)) n -
        Pi.π (fun n : ℕ ↦ (K ⋙ R).obj (⟨n⟩ : ℕᵒᵖ)) (n + 1) ≫
          (K ⋙ R).map (homOfLE (Nat.le_succ n)).op) δ'
    have hT : T' ∈ distTriang (DerivedCategory P) := hT'
    have hepi : Epi (E.map ((DerivedCategory.homologyFunctor P (m - 1)).map T'.mor₂)) :=
      epi_map_difference (K ⋙ R)
        (DerivedCategory.homologyFunctor P (m - 1) ⋙ E) (hlimOne U hU)
    have : Mono ((DerivedCategory.homologyFunctor P m ⋙ E).map T'.mor₁) :=
      _root_.mono_homology_eval_of_epi E T' hT m
    have hproj : Mono ((DerivedCategory.homologyFunctor P m ⋙ E).map
        (T'.mor₁ ≫ Pi.π (fun n : ℕ ↦ (K ⋙ R).obj (⟨n⟩ : ℕᵒᵖ)) n₀)) :=
      mono_projection_of_difference (K ⋙ R) T'.mor₁ (comp_distTriang_mor_zero₁₂ T' hT)
        (DerivedCategory.homologyFunctor P m ⋙ E) n₀ (hinj U hU)
    have hπ : T'.mor₁ ≫ Pi.π (fun n : ℕ ↦ (K ⋙ R).obj (⟨n⟩ : ℕᵒᵖ)) n₀ =
        R.map (p ≫ Pi.π (fun n : ℕ ↦ K.obj (⟨n⟩ : ℕᵒᵖ)) n₀) := by
      change (R.map p ≫ piComparison R (fun n : ℕ ↦ K.obj (⟨n⟩ : ℕᵒᵖ))) ≫
        Pi.π (fun n : ℕ ↦ R.obj (K.obj (⟨n⟩ : ℕᵒᵖ))) n₀ = _
      rw [Category.assoc, piComparison_comp_π, ← R.map_comp]
    rwa [hπ] at hproj
  have hstalk : Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf O.obj).map (H.map φ))) := by
    refine mono_stalkFunctor_map_of_nhds_basis x 𝔘 hbasis _ fun U hU ↦ ?_
    have := hmono U hU
    exact Functor.map_mono (forget₂ (ModuleCat.{u} (O.obj.obj (Opposite.op U)))
      AddCommGrpCat.{u}) _
  let T : SheafOfModules.{u} O ⥤ AddCommGrpCat.{u} :=
    SheafOfModules.forget O ⋙ PresheafOfModules.toPresheaf O.obj ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have hsheafify : Mono (((H ⋙ PresheafOfModules.sheafification (𝟙 O.obj)) ⋙ T).map φ) := by
    change Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (CategoryTheory.sheafifyMap (Opens.grothendieckTopology X)
        ((PresheafOfModules.toPresheaf O.obj).map (H.map φ))))
    exact mono_stalkFunctor_map_sheafifyMap x _ hstalk
  let e := sheafificationCohomologyPresheafIso O m
  exact (NatIso.mono_map_iff (Functor.isoWhiskerRight e T) φ).1 hsheafify

/-! ### Convergence of the truncation tower -/

/-- An inverse system of modules indexed by `ℕ` whose transition maps are invertible from some
stage on has vanishing first derived inverse limit: the difference endomorphism
`(xₙ) ↦ (xₙ - xₙ₊₁)` of the product is surjective. -/
private lemma isZero_cokernel_difference_moduleCat_of_eventually_iso
    {Rng : Type u} [Ring Rng] (F : ℕᵒᵖ ⥤ ModuleCat.{u} Rng) (N : ℕ)
    (h : ∀ n, N ≤ n → IsIso (F.map (homOfLE (Nat.le_succ n)).op)) :
    IsZero (cokernel (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op)) := by
  have hz := isZero_cokernel_difference_of_eventually_iso
    (F ⋙ forget₂ (ModuleCat.{u} Rng) AddCommGrpCat.{u}) N (fun n hn ↦ by
      have := h n hn
      exact Functor.map_isIso (forget₂ (ModuleCat.{u} Rng) AddCommGrpCat.{u})
        (F.map (homOfLE (Nat.le_succ n)).op))
  have := (forget₂ (ModuleCat.{u} Rng) AddCommGrpCat.{u}).epi_of_epi_map
    (epi_map_difference F (forget₂ (ModuleCat.{u} Rng) AddCommGrpCat.{u}) hz)
  exact isZero_cokernel_of_epi _

/-- Shifting a sheaf of modules into degree `a` shifts the degree of its cohomology over an open
by `a`: the sections over `U` of `Hʳ` of derived sections of `M` placed in degree `a` are
`H^{r-a}(U, M)`. -/
private lemma isZero_evaluation_homology_derivedSections_single {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} O)]
    [HasDerivedCategory.{wP} (PresheafOfModules.{u} O.obj)]
    (U : Opens X) (M : SheafOfModules.{u} O) (a r : ℤ)
    (h : IsZero ((PresheafOfModules.evaluation O.obj (Opposite.op U)).obj
      ((DerivedCategory.homologyFunctor (PresheafOfModules.{u} O.obj) (r - a)).obj
        ((derivedSectionsPresheaf O).obj
          ((DerivedCategory.singleFunctor (SheafOfModules.{u} O) 0).obj M))))) :
    IsZero ((PresheafOfModules.evaluation O.obj (Opposite.op U)).obj
      ((DerivedCategory.homologyFunctor (PresheafOfModules.{u} O.obj) r).obj
        ((derivedSectionsPresheaf O).obj
          ((DerivedCategory.singleFunctor (SheafOfModules.{u} O) a).obj M)))) := by
  have hGA : IsGrothendieckAbelian.{u} (SheafOfModules.{u} O) :=
    Stacks.SheafOfModules.sheafModulesGrothendieck _ O
  let A := SheafOfModules.{u} O
  let P := PresheafOfModules.{u} O.obj
  let R := derivedSectionsPresheaf O
  let α := (homotopySectionsPresheaf O).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
  let := Functor.IsRightDerivedFunctor.commShift R α
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ℤ
  let e : (DerivedCategory.singleFunctor A a).obj M ≅
      ((DerivedCategory.singleFunctor A 0).obj M)⟦-a⟧ :=
    ((DerivedCategory.singleFunctors A).shiftIso (-a) a 0 (by omega)).symm.app M
  refine h.of_iso ((PresheafOfModules.evaluation O.obj (Opposite.op U)).mapIso
    ((DerivedCategory.homologyFunctor P r).mapIso
      (R.mapIso e ≪≫ (R.commShiftIso (-a)).app _) ≪≫
      ((DerivedCategory.homologyFunctor P 0).shiftIso (-a) r (r - a) (by omega)).app _))

/-- If the cohomology of `U` with coefficients in `Hᵃ(E)` placed in degree `a` vanishes in degrees
`r` and `r + 1`, then the canonical map `τ_{≥ a} E ⟶ τ_{≥ a+1} E` is an isomorphism on the
degree-`r` cohomology of sections over `U`. -/
private lemma isIso_evaluation_homology_derivedSections_truncGEOfLE {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} O)]
    [HasDerivedCategory.{wP} (PresheafOfModules.{u} O.obj)]
    (E : DerivedCategory (SheafOfModules.{u} O)) (U : Opens X) (a b r : ℤ) (hab : a + 1 = b)
    (h₀ : IsZero ((PresheafOfModules.evaluation O.obj (Opposite.op U)).obj
      ((DerivedCategory.homologyFunctor (PresheafOfModules.{u} O.obj) r).obj
        ((derivedSectionsPresheaf O).obj
          ((DerivedCategory.singleFunctor (SheafOfModules.{u} O) a).obj
            ((DerivedCategory.homologyFunctor (SheafOfModules.{u} O) a).obj E))))))
    (h₁ : IsZero ((PresheafOfModules.evaluation O.obj (Opposite.op U)).obj
      ((DerivedCategory.homologyFunctor (PresheafOfModules.{u} O.obj) (r + 1)).obj
        ((derivedSectionsPresheaf O).obj
          ((DerivedCategory.singleFunctor (SheafOfModules.{u} O) a).obj
            ((DerivedCategory.homologyFunctor (SheafOfModules.{u} O) a).obj E)))))) :
    IsIso ((PresheafOfModules.evaluation O.obj (Opposite.op U)).map
      ((DerivedCategory.homologyFunctor (PresheafOfModules.{u} O.obj) r).map
        ((derivedSectionsPresheaf O).map
          ((DerivedCategory.TStructure.t.natTransTruncGEOfLE a b (by omega)).app E)))) := by
  subst hab
  have hGA : IsGrothendieckAbelian.{u} (SheafOfModules.{u} O) :=
    Stacks.SheafOfModules.sheafModulesGrothendieck _ O
  let A := SheafOfModules.{u} O
  let R := derivedSectionsPresheaf O
  let α := (homotopySectionsPresheaf O).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
  let := Functor.IsRightDerivedFunctor.commShift R α
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ℤ
  have hRtri : R.IsTriangulated :=
    Stacks.Injectives.rightDerivedFunctor_isTriangulated (SheafOfModules.forget O) R α
  obtain ⟨f, δ, hT⟩ := DerivedCategory.exists_truncGESucc_triangle E a
  exact isIso_homology_eval_of_isZero (PresheafOfModules.evaluation O.obj (Opposite.op U))
    (R.mapTriangle.obj (Triangle.mk f
      ((DerivedCategory.TStructure.t.natTransTruncGEOfLE a (a + 1) (by omega)).app E) δ))
    (R.map_distinguished _ hT) r h₀ h₁

/-- **Convergence of the truncation tower, at a given derived limit, from local vanishing.** Let
`E` be an object of the derived category of sheaves of `𝒪_X`-modules on a ringed space, and
suppose every point `x` carries a function `p(x, -)` and a fundamental system `𝔘ₓ` of open
neighbourhoods on whose members `Hᵖ(U, H^{m-p}(E))` vanishes whenever `p > p(x, m)`. Then for
every derived limit `L` of the tower of truncations `τ_{≥ -n} E`, presented by `pr` and `hL`,
every canonical map `c : E ⟶ L` is an isomorphism. -/
public theorem isIso_to_isDerivedLimit_truncGETower_of_local_vanishing {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} O)]
    [HasDerivedCategory.{wP} (PresheafOfModules.{u} O.obj)]
    (E : DerivedCategory (SheafOfModules.{u} O))
    (hvanishing : ∀ x : X, ∃ (pb : ℤ → ℤ) (𝔘 : Set (Opens X)),
      (nhds x).HasBasis (fun U : Opens X ↦ U ∈ 𝔘) (fun U ↦ (U : Set X)) ∧
        ∀ U ∈ 𝔘, ∀ (p : ℕ) (m : ℤ), pb m < (p : ℤ) →
          IsZero ((PresheafOfModules.evaluation O.obj (Opposite.op U)).obj
            (cohomologyPresheaf O
              ((DerivedCategory.singleFunctor (SheafOfModules.{u} O) 0).obj
                ((DerivedCategory.homologyFunctor (SheafOfModules.{u} O)
                  (m - (p : ℤ))).obj E)) (p : ℤ))))
    (L : DerivedCategory (SheafOfModules.{u} O)) (c : E ⟶ L)
    (pr : L ⟶ ∏ᶜ fun n : ℕ ↦
      (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩)
    (hL : ∃ δ : (∏ᶜ fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk pr (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦
          (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦
            (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) (n + 1) ≫
            (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).map
              (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (SheafOfModules.{u} O)))
    (hc : ∀ n : ℕ, c ≫ pr ≫ Pi.π
      (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) n =
      (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) :
    IsIso c := by
  classical
  refine Stacks.Cohomology.StalkwiseIso.isIso_of_forall_stalkAddCommGroup_isIso O c ?_
  intro m x
  obtain ⟨pb, 𝔘, hbasis, hvan⟩ := hvanishing x
  let A := SheafOfModules.{u} O
  let P := PresheafOfModules.{u} O.obj
  let R := derivedSectionsPresheaf O
  let K := Stacks.DerivedLimit.truncGETower A E
  let N : ℕ := (max (-m) (max (pb (m - 1) - m)
    (max (pb m - m) (pb (m + 1) - m)))).toNat + 1
  have hN : -(N : ℤ) ≤ m := by dsimp only [N]; omega
  have hvanish3 : ∀ U ∈ 𝔘, ∀ (n : ℕ), N ≤ n → ∀ r : ℤ, m - 1 ≤ r → r ≤ m + 1 →
      IsZero ((PresheafOfModules.evaluation O.obj (Opposite.op U)).obj
        ((DerivedCategory.homologyFunctor P r).obj
          (R.obj ((DerivedCategory.singleFunctor A (-((n + 1 : ℕ) : ℤ))).obj
            ((DerivedCategory.homologyFunctor A (-((n + 1 : ℕ) : ℤ))).obj E))))) := by
    intro U hU n hn r hr₀ hr₁
    dsimp only [N] at hn
    obtain ⟨q, hq⟩ : ∃ q : ℕ, (q : ℤ) = r + 1 + n := ⟨(r + 1 + n).toNat, by omega⟩
    have hb : pb r < q := by
      obtain rfl | rfl | rfl : r = m - 1 ∨ r = m ∨ r = m + 1 := by omega
      all_goals omega
    have h := hvan U hU q r hb
    rw [show -((n + 1 : ℕ) : ℤ) = r - q by push_cast; omega]
    exact isZero_evaluation_homology_derivedSections_single O U _ (r - q) r
      (by rw [sub_sub_cancel]; exact h)
  have hiso : ∀ U ∈ 𝔘, ∀ (r : ℤ), m - 1 ≤ r → r ≤ m → ∀ n : ℕ, N ≤ n →
      IsIso ((PresheafOfModules.evaluation O.obj (Opposite.op U)).map
        ((DerivedCategory.homologyFunctor P r).map
          (R.map (K.map (homOfLE (Nat.le_succ n)).op)))) := by
    intro U hU r hr₀ hr₁ n hn
    rw [Stacks.DerivedLimit.truncGETower_map_homOfLE_succ]
    exact isIso_evaluation_homology_derivedSections_truncGEOfLE O E U
      (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) r (by push_cast; ring)
      (hvanish3 U hU n hn r (by omega) (by omega))
      (hvanish3 U hU n hn (r + 1) (by omega) (by omega))
  have hmono := cohomology_derivedLimit_projection_mono_on_stalk O K L pr hL x m N 𝔘 hbasis
    (fun U hU ↦ isZero_cokernel_difference_moduleCat_of_eventually_iso
      (K ⋙ R ⋙ DerivedCategory.homologyFunctor P (m - 1) ⋙
        PresheafOfModules.evaluation O.obj (Opposite.op U)) N
      (fun n hn ↦ hiso U hU (m - 1) (by omega) (by omega) n hn))
    (fun U hU n hn ↦ by
      have := isIso_map_to_of_successive_isIso
        (K ⋙ R ⋙ DerivedCategory.homologyFunctor P m ⋙
          PresheafOfModules.evaluation O.obj (Opposite.op U)) N
        (fun n hn ↦ hiso U hU m (by omega) le_rfl n hn) n hn
      infer_instance)
  let S := AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor O x
  let H := DerivedCategory.homologyFunctor A m
  have hmono' : Mono (S.map (H.map (pr ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) N))) := hmono
  have hcomp : IsIso (S.map (H.map c) ≫
      S.map (H.map (pr ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) N))) := by
    rw [← S.map_comp, ← H.map_comp, hc N]
    have := DerivedCategory.isIso_homologyMap_truncGEπ_app (-(N : ℤ)) m hN E
    exact Functor.map_isIso S (H.map ((DerivedCategory.TStructure.t.truncGEπ (-(N : ℤ))).app E))
  have : Epi (S.map (H.map (pr ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) N))) :=
    epi_of_epi (S.map (H.map c)) _
  have : IsIso (S.map (H.map (pr ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) N))) := isIso_of_mono_of_epi _
  exact (isIso_comp_right_iff (S.map (H.map c)) _).1 hcomp

/-! ### Convergence from a global vanishing hypothesis -/

/-- If every open of a topological space is the union of a family of members of a set `𝔅` of
opens, then for each point `x` the members of `𝔅` containing `x` form a fundamental system of
open neighbourhoods of `x`. -/
private lemma hasBasis_nhds_of_cover {X : TopCat.{u}} (x : X) (𝔅 : Set (Opens X))
    (hcov : ∀ V : Opens X, ∃ 𝒰 : Set (Opens X), 𝒰 ⊆ 𝔅 ∧ (V : Set X) = ⋃ U ∈ 𝒰, (U : Set X)) :
    (nhds x).HasBasis (fun U : Opens X ↦ U ∈ {U : Opens X | U ∈ 𝔅 ∧ x ∈ U})
      (fun U ↦ (U : Set X)) := by
  constructor
  intro t
  constructor
  · intro ht
    obtain ⟨V, hVt, hVopen, hxV⟩ := mem_nhds_iff.mp ht
    obtain ⟨𝒰, h𝒰, hunion⟩ := hcov ⟨V, hVopen⟩
    obtain ⟨U, hU𝒰, hxU⟩ := Set.mem_iUnion₂.mp (hunion ▸ hxV : x ∈ ⋃ U ∈ 𝒰, (U : Set X))
    refine ⟨U, ⟨h𝒰 hU𝒰, hxU⟩, subset_trans ?_ hVt⟩
    have hUV : (U : Set X) ⊆ ⋃ W ∈ 𝒰, (W : Set X) := Set.subset_biUnion_of_mem hU𝒰
    rwa [← hunion] at hUV
  · rintro ⟨U, ⟨-, hxU⟩, hUt⟩
    exact mem_nhds_iff.mpr ⟨U, hUt, U.isOpen, hxU⟩

/-- **Convergence of the truncation tower, at a given derived limit, from vanishing on a covering
family.** Let `E` be an object of the derived category of sheaves of `𝒪_X`-modules on a ringed
space, let `p(-)` be a function and let `𝔅` be a set of opens of `X` such that every open of `X`
is a union of members of `𝔅` and `Hᵖ(U, H^{m-p}(E))` vanishes for `U ∈ 𝔅` and `p > p(m)`. Then
for every derived limit `L` of the tower of truncations `τ_{≥ -n} E`, presented by `pr` and
`hL`, every canonical map `c : E ⟶ L` is an isomorphism. -/
public theorem isIso_to_isDerivedLimit_truncGETower_of_vanishing_on_cover {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} O)]
    [HasDerivedCategory.{wP} (PresheafOfModules.{u} O.obj)]
    (E : DerivedCategory (SheafOfModules.{u} O))
    (pb : ℤ → ℤ) (𝔅 : Set (Opens X))
    (hcov : ∀ V : Opens X, ∃ 𝒰 : Set (Opens X), 𝒰 ⊆ 𝔅 ∧ (V : Set X) = ⋃ U ∈ 𝒰, (U : Set X))
    (hvanishing : ∀ U ∈ 𝔅, ∀ (p : ℕ) (m : ℤ), pb m < (p : ℤ) →
      IsZero ((PresheafOfModules.evaluation O.obj (Opposite.op U)).obj
        (cohomologyPresheaf O
          ((DerivedCategory.singleFunctor (SheafOfModules.{u} O) 0).obj
            ((DerivedCategory.homologyFunctor (SheafOfModules.{u} O)
              (m - (p : ℤ))).obj E)) (p : ℤ))))
    (L : DerivedCategory (SheafOfModules.{u} O)) (c : E ⟶ L)
    (pr : L ⟶ ∏ᶜ fun n : ℕ ↦
      (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩)
    (hL : ∃ δ : (∏ᶜ fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk pr (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦
          (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦
            (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) (n + 1) ≫
            (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).map
              (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (SheafOfModules.{u} O)))
    (hc : ∀ n : ℕ, c ≫ pr ≫ Pi.π
      (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) n =
      (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) :
    IsIso c :=
  isIso_to_isDerivedLimit_truncGETower_of_local_vanishing O E
    (fun x ↦ ⟨pb, {U : Opens X | U ∈ 𝔅 ∧ x ∈ U}, hasBasis_nhds_of_cover x 𝔅 hcov,
      fun U hU ↦ hvanishing U hU.1⟩) L c pr hL hc

/-- **The truncation tower of an object of `D(𝒪_X)` always has a presented derived limit, and
the canonical map to it is pinned.** For every ringed space and every `E`, the tower
`τ_{≥ -n} E` has a product, a derived limit `L` presented by its defining distinguished
triangle, and a map `c : E ⟶ L` all of whose composites with the projections of that triangle
are the canonical truncation maps `τ_{≥ -n}π`. No hypothesis on `E` or on `X` is needed.

This is what makes the universally quantified datum of
`isIso_to_isDerivedLimit_truncGETower_of_local_vanishing` and of
`isIso_to_isDerivedLimit_truncGETower_of_vanishing_on_cover` inhabited, so that their
conclusions are assertions about a map that exists rather than about an empty family. -/
theorem exists_presented_derivedLimit_truncGETower {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} O)]
    (E : DerivedCategory (SheafOfModules.{u} O)) :
    ∃ (_ : HasProduct fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩)
      (L : DerivedCategory (SheafOfModules.{u} O)) (c : E ⟶ L)
      (pr : L ⟶ ∏ᶜ fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩),
      (∃ δ : (∏ᶜ fun n : ℕ ↦
          (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
        Triangle.mk pr (Pi.lift fun n : ℕ ↦
          Pi.π (fun n : ℕ ↦
            (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) n -
            Pi.π (fun n : ℕ ↦
              (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) (n + 1) ≫
              (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).map
                (homOfLE (Nat.le_succ n)).op) δ ∈
          distTriang (DerivedCategory (SheafOfModules.{u} O))) ∧
      (∀ n : ℕ, c ≫ pr ≫ Pi.π
        (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) n =
        (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) := by
  have hGA : IsGrothendieckAbelian.{u} (SheafOfModules.{u} O) :=
    Stacks.SheafOfModules.sheafModulesGrothendieck _ O
  let _ : HasLimitsOfShape (Discrete ℕ) (SheafOfModules.{u} O) :=
    SheafOfModules.hasLimitsOfShape.{u} (R := O) (Discrete ℕ)
  let _ : HasProductsOfShape ℕ (SheafOfModules.{u} O) := inferInstance
  let tower := Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E
  obtain ⟨hprod, L, pr, δ, hT⟩ := DerivedCategory.exists_isDerivedLimit_of_forall_isGE tower
    (fun n ↦ ⟨-(n : ℤ), by
      change ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E).IsGE _
      infer_instance⟩)
  let _ := hprod
  let q : E ⟶ ∏ᶜ fun n : ℕ ↦ tower.obj ⟨n⟩ :=
    Pi.lift (fun n ↦ (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E)
  let diff := Pi.lift fun n : ℕ ↦
    Pi.π (fun n : ℕ ↦ tower.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ ↦ tower.obj ⟨n⟩) (n + 1) ≫ tower.map (homOfLE (Nat.le_succ n)).op
  let T := Triangle.mk pr diff δ
  have hq (n : ℕ) : q ≫ Pi.π (fun n : ℕ ↦ tower.obj ⟨n⟩) n =
      (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E := Pi.lift_comp_π _ n
  have hzero : q ≫ T.mor₂ = 0 := by
    change q ≫ diff = 0
    refine Pi.hom_ext _ _ fun n ↦ ?_
    rw [Category.assoc, Pi.lift_comp_π, Preadditive.comp_sub, hq n, ← Category.assoc, hq (n + 1),
      Stacks.DerivedLimit.truncGETower_map_homOfLE_succ, zero_comp]
    exact sub_eq_zero_of_eq
      (DerivedCategory.TStructure.t.π_natTransTruncGEOfLE_app _ _ (by omega) E).symm
  obtain ⟨c, hc⟩ := T.coyoneda_exact₂ hT q hzero
  change q = c ≫ pr at hc
  exact ⟨hprod, L, c, pr, ⟨δ, hT⟩, fun n ↦ by rw [← Category.assoc, ← hc]; exact Pi.lift_comp_π _ n⟩

/-- **Stacks Project, Tag 08U2**, in the form the source states it: the canonical map
`E ⟶ R lim τ_{≥ -n} E` *is* an isomorphism. The derived limit and the canonical map are
constructed by `exists_presented_derivedLimit_truncGETower`. -/
@[stacks 08U2 "the conclusion with the derived limit and the canonical map of Remark 0H72 \
constructed rather than quantified over"]
theorem exists_isIso_to_derivedLimit_truncGETower_of_vanishing_on_cover {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} O)]
    [HasDerivedCategory.{wP} (PresheafOfModules.{u} O.obj)]
    (E : DerivedCategory (SheafOfModules.{u} O))
    (pb : ℤ → ℤ) (𝔅 : Set (Opens X))
    (hcov : ∀ V : Opens X, ∃ 𝒰 : Set (Opens X), 𝒰 ⊆ 𝔅 ∧ (V : Set X) = ⋃ U ∈ 𝒰, (U : Set X))
    (hvanishing : ∀ U ∈ 𝔅, ∀ (p : ℕ) (m : ℤ), pb m < (p : ℤ) →
      IsZero ((PresheafOfModules.evaluation O.obj (Opposite.op U)).obj
        (cohomologyPresheaf O
          ((DerivedCategory.singleFunctor (SheafOfModules.{u} O) 0).obj
            ((DerivedCategory.homologyFunctor (SheafOfModules.{u} O)
              (m - (p : ℤ))).obj E)) (p : ℤ)))) :
    ∃ (_ : HasProduct fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩)
      (L : DerivedCategory (SheafOfModules.{u} O)) (c : E ⟶ L)
      (pr : L ⟶ ∏ᶜ fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩),
      (∃ δ : (∏ᶜ fun n : ℕ ↦
          (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
        Triangle.mk pr (Pi.lift fun n : ℕ ↦
          Pi.π (fun n : ℕ ↦
            (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) n -
            Pi.π (fun n : ℕ ↦
              (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) (n + 1) ≫
              (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).map
                (homOfLE (Nat.le_succ n)).op) δ ∈
          distTriang (DerivedCategory (SheafOfModules.{u} O))) ∧
      (∀ n : ℕ, c ≫ pr ≫ Pi.π
        (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) n =
        (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) ∧ IsIso c := by
  obtain ⟨hprod, L, c, pr, hL, hc⟩ := exists_presented_derivedLimit_truncGETower O E
  exact ⟨hprod, L, c, pr, hL, hc, isIso_to_isDerivedLimit_truncGETower_of_vanishing_on_cover
    O E pb 𝔅 hcov hvanishing L c pr hL hc⟩

/-- **Stacks Project, Tag 0D62.** Let `E` be an object of the derived category of sheaves of
`𝒪_X`-modules on a ringed space, and suppose every point `x` carries a function `p(x, -)` and a
fundamental system `𝔘ₓ` of open neighbourhoods on whose members `Hᵖ(U, H^{m-p}(E))` vanishes
whenever `p > p(x, m)`. Then the tower of truncations `τ_{≥ -n} E` from below has a derived
limit `R lim τ_{≥ -n} E` with a canonical map of Remark 0H72 from `E`, and every such canonical
map to every derived limit of the tower is an isomorphism. -/
@[stacks 0D62 "the derived limit and the canonical map of Remark 0H72 exist, and every such \
canonical map is an isomorphism"]
public theorem exists_and_forall_isIso_to_derivedLimit_truncGETower_of_local_vanishing
    {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} O)]
    [HasDerivedCategory.{wP} (PresheafOfModules.{u} O.obj)]
    (E : DerivedCategory (SheafOfModules.{u} O))
    (hvanishing : ∀ x : X, ∃ (pb : ℤ → ℤ) (𝔘 : Set (Opens X)),
      (nhds x).HasBasis (fun U : Opens X ↦ U ∈ 𝔘) (fun U ↦ (U : Set X)) ∧
        ∀ U ∈ 𝔘, ∀ (p : ℕ) (m : ℤ), pb m < (p : ℤ) →
          IsZero ((PresheafOfModules.evaluation O.obj (Opposite.op U)).obj
            (cohomologyPresheaf O
              ((DerivedCategory.singleFunctor (SheafOfModules.{u} O) 0).obj
                ((DerivedCategory.homologyFunctor (SheafOfModules.{u} O)
                  (m - (p : ℤ))).obj E)) (p : ℤ)))) :
    (∃ (_ : HasProduct fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩)
      (L : DerivedCategory (SheafOfModules.{u} O)) (c : E ⟶ L)
      (pr : L ⟶ ∏ᶜ fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩),
      (∃ δ : (∏ᶜ fun n : ℕ ↦
          (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
        Triangle.mk pr (Pi.lift fun n : ℕ ↦
          Pi.π (fun n : ℕ ↦
            (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) n -
            Pi.π (fun n : ℕ ↦
              (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) (n + 1) ≫
              (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).map
                (homOfLE (Nat.le_succ n)).op) δ ∈
          distTriang (DerivedCategory (SheafOfModules.{u} O))) ∧
      (∀ n : ℕ, c ≫ pr ≫ Pi.π
        (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) n =
        (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E)) ∧
    ∀ (L : DerivedCategory (SheafOfModules.{u} O)) (c : E ⟶ L)
      (pr : L ⟶ ∏ᶜ fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩),
      (∃ δ : (∏ᶜ fun n : ℕ ↦
          (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
        Triangle.mk pr (Pi.lift fun n : ℕ ↦
          Pi.π (fun n : ℕ ↦
            (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) n -
            Pi.π (fun n : ℕ ↦
              (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) (n + 1) ≫
              (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).map
                (homOfLE (Nat.le_succ n)).op) δ ∈
          distTriang (DerivedCategory (SheafOfModules.{u} O))) →
      (∀ n : ℕ, c ≫ pr ≫ Pi.π
        (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) n =
        (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) →
      IsIso c :=
  ⟨exists_presented_derivedLimit_truncGETower O E, fun L c pr hL hc ↦
    isIso_to_isDerivedLimit_truncGETower_of_local_vanishing O E hvanishing L c pr hL hc⟩

/-- **Stacks Project, Tag 08U2.** Let `E` be an object of the derived category of sheaves of
`𝒪_X`-modules on a ringed space, let `p(-)` be a function and let `𝔅` be a set of opens of `X`
such that every open of `X` is a union of members of `𝔅` and `Hᵖ(U, H^{m-p}(E))` vanishes for
`U ∈ 𝔅` and `p > p(m)`. Then the tower of truncations `τ_{≥ -n} E` from below has a derived
limit `R lim τ_{≥ -n} E` with a canonical map of Remark 0H72 from `E`, and every such canonical
map to every derived limit of the tower is an isomorphism. -/
@[stacks 08U2 "the derived limit and the canonical map of Remark 0H72 exist, and every such \
canonical map is an isomorphism"]
public theorem exists_and_forall_isIso_to_derivedLimit_truncGETower_of_vanishing_on_cover
    {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} O)]
    [HasDerivedCategory.{wP} (PresheafOfModules.{u} O.obj)]
    (E : DerivedCategory (SheafOfModules.{u} O))
    (pb : ℤ → ℤ) (𝔅 : Set (Opens X))
    (hcov : ∀ V : Opens X, ∃ 𝒰 : Set (Opens X), 𝒰 ⊆ 𝔅 ∧ (V : Set X) = ⋃ U ∈ 𝒰, (U : Set X))
    (hvanishing : ∀ U ∈ 𝔅, ∀ (p : ℕ) (m : ℤ), pb m < (p : ℤ) →
      IsZero ((PresheafOfModules.evaluation O.obj (Opposite.op U)).obj
        (cohomologyPresheaf O
          ((DerivedCategory.singleFunctor (SheafOfModules.{u} O) 0).obj
            ((DerivedCategory.homologyFunctor (SheafOfModules.{u} O)
              (m - (p : ℤ))).obj E)) (p : ℤ)))) :
    (∃ (_ : HasProduct fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩)
      (L : DerivedCategory (SheafOfModules.{u} O)) (c : E ⟶ L)
      (pr : L ⟶ ∏ᶜ fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩),
      (∃ δ : (∏ᶜ fun n : ℕ ↦
          (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
        Triangle.mk pr (Pi.lift fun n : ℕ ↦
          Pi.π (fun n : ℕ ↦
            (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) n -
            Pi.π (fun n : ℕ ↦
              (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) (n + 1) ≫
              (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).map
                (homOfLE (Nat.le_succ n)).op) δ ∈
          distTriang (DerivedCategory (SheafOfModules.{u} O))) ∧
      (∀ n : ℕ, c ≫ pr ≫ Pi.π
        (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) n =
        (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E)) ∧
    ∀ (L : DerivedCategory (SheafOfModules.{u} O)) (c : E ⟶ L)
      (pr : L ⟶ ∏ᶜ fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩),
      (∃ δ : (∏ᶜ fun n : ℕ ↦
          (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
        Triangle.mk pr (Pi.lift fun n : ℕ ↦
          Pi.π (fun n : ℕ ↦
            (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) n -
            Pi.π (fun n : ℕ ↦
              (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) (n + 1) ≫
              (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).map
                (homOfLE (Nat.le_succ n)).op) δ ∈
          distTriang (DerivedCategory (SheafOfModules.{u} O))) →
      (∀ n : ℕ, c ≫ pr ≫ Pi.π
        (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower (SheafOfModules.{u} O) E).obj ⟨n⟩) n =
        (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) →
      IsIso c :=
  ⟨exists_presented_derivedLimit_truncGETower O E, fun L c pr hL hc ↦
    isIso_to_isDerivedLimit_truncGETower_of_vanishing_on_cover O E pb 𝔅 hcov hvanishing L c pr
      hL hc⟩

end Stacks.Cohomology.DerivedLimitStalk

end
