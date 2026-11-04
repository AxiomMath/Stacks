module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductInclusion
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.CategoryOfFppfTorsors
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.CategoryOfSheafTorsors
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FppfCoverings

/-!
# Comparing fppf torsors of algebraic spaces with torsors of sheaves

Let `B` be an algebraic space over a scheme `S` and let `G` be a group algebraic space over `B`.
Write `𝒢`, resp. `ℬ` for `G`, resp. `B` seen as a sheaf on the big fppf site of `S`. The functor
`G-Torsors ⟶ 𝒢/ℬ-Torsors` of Stacks 04UT sends a triple `(U, b, X)` to the triple `(U, b, 𝒳)`
with `𝒳` the total space `X` viewed as a sheaf, and a morphism to the same morphism. It is a
1-morphism of categories over `(Sch/S)_fppf` and it is fully faithful, because the algebraic
spaces over `S` form a full subcategory of the sheaves on the big fppf site of `S`.

## Main definitions

* `AlgebraicGeometry.Space.FppfTorsors.toSheafTorsors`: an fppf torsor of algebraic spaces,
  viewed as a torsor of sheaves.
* `AlgebraicGeometry.Space.FppfTorsors.comparison`: the comparison functor
  `G-Torsors ⥤ 𝒢/ℬ-Torsors`.

## Main results

* `AlgebraicGeometry.Space.isLocallySurjective_of_fppfCovering_sections`: an object over an
  algebraic space which acquires a section after an fppf covering of the base has sections
  locally on the base.
* `AlgebraicGeometry.Space.FppfTorsors.comparison_comp_projection`: the comparison functor is
  a 1-morphism of categories over the big fppf site of `S`.
* `AlgebraicGeometry.Space.FppfTorsors.instFullComparison` and
  `AlgebraicGeometry.Space.FppfTorsors.instFaithfulComparison`: the comparison functor is fully
  faithful.

## Implementation notes

An object of either category carries a base object `U` of the site, a section `b` of `ℬ` over
`U`, an object `total` of `Over (yoneda.obj U)` and an action of the base change of the group
along `b`, and the two acting groups are the same. So the comparison functor only replaces the
fppf torsor condition of Stacks 04TY by the sheaf-theoretic torsor condition of Stacks 03AH, and
a morphism of either category is the same tuple.

## References

* [Stacks Project, Tag 04UT](https://stacks.math.columbia.edu/tag/04UT)
* [Stacks Project, Tag 04UL](https://stacks.math.columbia.edu/tag/04UL)
* [Stacks Project, Tag 04UR](https://stacks.math.columbia.edu/tag/04UR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory MonObj

universe u

namespace AlgebraicGeometry.Space

open TorsorsFor hiding projection

/-- An object over a representable algebraic space whose structure morphism has a section after
an fppf covering of the base has sections locally on the base: its structure morphism is
locally surjective for the fppf topology. -/
@[sga "3 IV 6.7.3" "(i)(2), special case"]
theorem isLocallySurjective_of_fppfCovering_sections (𝒞 : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : 𝒞.Contains S) (U : BigFppfOver 𝒞 S hS) (X : Over (yoneda.obj U))
    {I : Type (u + 1)} (Bi : I → (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (f : ∀ i, Bi i ⟶ yoneda.obj U) (hcover : IsFppfCovering 𝒞 S hS Bi f)
    (hsections : ∀ i, Nonempty (𝟙_ (Over (Bi i)) ⟶ (Over.pullback (f i)).obj X)) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology 𝒞 S hS) X.hom := by
  classical
  have hsec : ∀ i, ∃ t : Bi i ⟶ X.left, t ≫ X.hom = f i := by
    intro i
    obtain ⟨s⟩ := hsections i
    refine ⟨s.left ≫ pullback.fst X.hom (f i), ?_⟩
    have hw : s.left ≫ pullback.snd X.hom (f i) = 𝟙 (Bi i) := by simpa using Over.w s
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw, Category.id_comp]
  choose t ht using hsec
  refine ⟨?_⟩
  intro V x
  set v : V ⟶ U := x with hv
  set g : yoneda.obj V ⟶ yoneda.obj U := yoneda.map v with hg
  let Xspace (i : I) : AlgebraicSpaces 𝒞 S hS := ⟨Bi i, hcover.source_isAlgebraicSpace i⟩
  let Vspace : AlgebraicSpaces 𝒞 S hS := ⟨yoneda.obj V, isAlgebraicSpace_yoneda 𝒞 S hS V⟩
  let Uspace : AlgebraicSpaces 𝒞 S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda 𝒞 S hS U⟩
  let fspace (i : I) : Xspace i ⟶ Uspace := ObjectProperty.homMk (f i)
  let gspace : Vspace ⟶ Uspace := ObjectProperty.homMk g
  have hY : IsFppfCovering 𝒞 S hS
      (fun i => (AlgebraicSpaces.fiberProduct 𝒞 S hS gspace (fspace i)).1)
      (fun i => pullback.fst gspace.hom (fspace i).hom) :=
    isFppfCovering_fibreProduct 𝒞 S hS Xspace fspace gspace hcover
  obtain ⟨T, a, hT⟩ := exists_fppfCovering_scheme_refinement 𝒞 S hS _ _ hY
  let p₁ (i : I) : (AlgebraicSpaces.fiberProduct 𝒞 S hS gspace (fspace i)).1 ⟶ yoneda.obj V :=
    pullback.fst gspace.hom (fspace i).hom
  let p₂ (i : I) : (AlgebraicSpaces.fiberProduct 𝒞 S hS gspace (fspace i)).1 ⟶ Bi i :=
    pullback.snd gspace.hom (fspace i).hom
  let q (i : I) : T i ⟶ V := yonedaEquiv (a i ≫ p₁ i)
  have hproj : ∀ i, a i ≫ p₁ i = yoneda.map (q i) := by
    intro i
    apply (yonedaEquiv (X := T i) (F := yoneda.obj V)).injective
    simp only [q, yonedaEquiv_yoneda_map]
  have hT' : IsFppfCovering 𝒞 S hS (fun i => yoneda.obj (T i)) (fun i => yoneda.map (q i)) := by
    simpa only [← hproj] using hT
  let E : PreZeroHypercover.{u + 1} V.left := ⟨I, fun i => (T i).left, fun i => (q i).left⟩
  have htop : Sieve.generate E.presieve₀ ∈ 𝒞.topology V.left := by
    refine 𝒞.generate_mem_topology_of_isFppfCovering E ?_
    rw [AlgebraicGeometry.IsFppfCovering, Precoverage.mem_comap_iff,
      ← PreZeroHypercover.presieve₀_map]
    exact yoneda_fppfCovering_mem_fppfPrecoverage 𝒞 S hS T V q hT'
  have hR₀ : Sieve.ofArrows T q ∈ BigFppfOver.topology 𝒞 S hS V := by
    rw [BigFppfOver.topology, GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    simpa [E, PreZeroHypercover.presieve₀] using htop
  refine (BigFppfOver.topology 𝒞 S hS).superset_covering ?_ hR₀
  intro W k hk
  obtain ⟨i, e, he⟩ := Sieve.ofArrows.exists hk
  refine ⟨yonedaEquiv (yoneda.map e ≫ a i ≫ p₂ i ≫ t i), ?_⟩
  have hcond : p₂ i ≫ f i = p₁ i ≫ g := (pullback.condition (f := gspace.hom)).symm
  have hfac : a i ≫ p₂ i ≫ t i ≫ X.hom = yoneda.map (q i) ≫ g := by
    rw [ht i, hcond, ← Category.assoc, hproj i]
  rw [← yonedaEquiv_comp]
  simp only [Category.assoc]
  rw [hfac, hg, ← Functor.map_comp, ← Functor.map_comp, yonedaEquiv_yoneda_map, he]
  simp

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} {hB : IsAlgebraicSpace 𝒞 S hS B}
  {G : GroupAlgebraicSpace 𝒞 S hS B hB}

namespace FppfTorsors

/-- The total space of an fppf torsor of algebraic spaces has sections locally on its base. -/
theorem isLocallySurjective (T : FppfTorsors hB G) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology 𝒞 S hS) T.total.hom := by
  obtain ⟨I, Bi, f, -, hcover, hsections⟩ := T.isTorsor.2
  exact isLocallySurjective_of_fppfCovering_sections 𝒞 S hS T.base T.total Bi f hcover hsections

/-- An fppf torsor of algebraic spaces under `G_U = U ×_{b, B} G` is a torsor of sheaves under
the same group, in the sense of Stacks 03AH for the localized site `(Sch/U)_fppf`. -/
theorem isSheafTorsor (T : FppfTorsors hB G) :
    IsSheafTorsor G.obj T.base T.sec T.total T.action :=
  ⟨T.isAlgebraicSpace.isSheaf, T.isTorsor.1, T.isLocallySurjective⟩

/-- An object `(U, b, X)` of `G-Torsors`, viewed as the object `(U, b, 𝒳)` of `𝒢/ℬ-Torsors`
whose total space is the total space of `X` seen as a sheaf. -/
def toSheafTorsors (T : FppfTorsors hB G) : SheafTorsors G.obj where
  base := T.base
  sec := T.sec
  total := T.total
  action := T.action
  isTorsor := T.isSheafTorsor

/-- A morphism of `G-Torsors`, viewed as a morphism of `𝒢/ℬ-Torsors` between the objects seen
as torsors of sheaves: it is the same pair of morphisms. -/
def toSheafTorsorsHom {T T' : FppfTorsors hB G} (φ : T ⟶ T') :
    T.toSheafTorsors ⟶ T'.toSheafTorsors where
  base := Hom.base φ
  comp_sec := Hom.comp_sec φ
  map := Hom.map φ
  isPullback := Hom.isPullback φ
  smul_comp := Hom.smul_comp φ

/-- The comparison functor `G-Torsors ⥤ 𝒢/ℬ-Torsors` which associates to a triple `(U, b, X)`
the triple `(U, b, 𝒳)` where `𝒳` is `X` viewed as a sheaf. -/
@[stacks 04UT "the comparison functor"]
def comparison (hB : IsAlgebraicSpace 𝒞 S hS B) (G : GroupAlgebraicSpace 𝒞 S hS B hB) :
    FppfTorsors hB G ⥤ SheafTorsors G.obj where
  obj T := T.toSheafTorsors
  map φ := toSheafTorsorsHom φ
  map_id _ := SheafTorsors.Hom.ext rfl rfl
  map_comp _ _ := SheafTorsors.Hom.ext rfl rfl

/-- The comparison functor sends an fppf torsor to the same torsor seen as a torsor of
sheaves. -/
@[simp]
theorem comparison_obj (T : FppfTorsors hB G) : (comparison hB G).obj T = T.toSheafTorsors :=
  rfl

/-- The comparison functor sends a morphism of fppf torsors to the same morphism of torsors of
sheaves. -/
@[simp]
theorem comparison_map {T T' : FppfTorsors hB G} (φ : T ⟶ T') :
    (comparison hB G).map φ = toSheafTorsorsHom φ :=
  rfl

/-- The comparison functor is a 1-morphism of categories over the big fppf site of `S`: it
sends a triple `(U, b, X)` to a triple with the same base object `U` and a morphism to a
morphism with the same morphism `f` of the site. -/
@[stacks 04UT "the comparison functor lies over the site"]
theorem comparison_comp_projection (hB : IsAlgebraicSpace 𝒞 S hS B)
    (G : GroupAlgebraicSpace 𝒞 S hS B hB) :
    comparison hB G ⋙ SheafTorsors.projection G.obj = projection hB G :=
  rfl

/-- The comparison functor is faithful: a morphism of `G-Torsors` is determined by the
morphism of `𝒢/ℬ-Torsors` it becomes. -/
@[stacks 04UT "the comparison functor is faithful"]
instance instFaithfulComparison : (comparison hB G).Faithful where
  map_injective h :=
    Hom.ext (congrArg SheafTorsors.Hom.base h) (congrArg SheafTorsors.Hom.map h)

/-- The comparison functor is full: a morphism of `𝒢/ℬ-Torsors` between torsors of algebraic
spaces is already a morphism of `G-Torsors`. -/
@[stacks 04UT "the comparison functor is full"]
instance instFullComparison : (comparison hB G).Full where
  map_surjective ψ :=
    ⟨{ base := SheafTorsors.Hom.base ψ
       comp_sec := SheafTorsors.Hom.comp_sec ψ
       map := SheafTorsors.Hom.map ψ
       isPullback := SheafTorsors.Hom.isPullback ψ
       smul_comp := SheafTorsors.Hom.smul_comp ψ },
      SheafTorsors.Hom.ext rfl rfl⟩

end FppfTorsors

end AlgebraicGeometry.Space

end
