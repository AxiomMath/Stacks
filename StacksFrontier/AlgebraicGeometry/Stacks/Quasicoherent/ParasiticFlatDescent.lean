module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticFlatLocalLifts
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticPullback

/-!
# Parasitic descends along a jointly surjective flat family (Stacks 0774)

Let `f j : 𝒳 j ⟶ 𝒴`, `j ∈ J`, be a family of 1-morphisms of algebraic stacks over `S` which are
each flat (**Stacks 06PW**) and locally of finite presentation (**Stacks 06Q2**) and which is
jointly surjective, that is `|𝒴| = ⋃ j |f j|(|𝒳 j|)`. Clause (4) of **Stacks 0774** says that a
sheaf of `𝒪_𝒴`-modules on the fppf site of `𝒴` is parasitic (**Stacks 0773**) as soon as every
inverse image `(f j)^*ℱ` is.

The source's proof — it says only that this case is "similar to but simpler than" clause (3) — is
the following. Let `y` be an object of `𝒴` lying over a scheme `U` with `y : U → 𝒴` flat. Form
the 2-fibre products `𝒳 j ×_𝒴 U`, cover each of them by a scheme smoothly and surjectively, and
let `x_i : W_i → 𝒳 (a i)` be the resulting projections. Each `x_i` is flat, being a smooth
morphism followed by the base change of the flat `y : U → 𝒴`, so `(f (a i))^*ℱ` vanishes at
`x_i`, that is `ℱ` vanishes at `f (a i)(x_i)`. The morphisms `W_i → U` are flat and locally of
finite presentation and are jointly surjective, so the family
`{f (a i)(x_i) → y}` is an fppf covering of `y`; since `ℱ` is an fppf sheaf and its sections
vanish along every member, they vanish at `y`.

The covering with its flat lifts is
`AlgebraicGeometry.Stack.exists_fppfCovering_family_flatObject_lift` of
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/ParasiticFlatLocalLifts.lean`, which is
**Stacks 07AN** with the extra conclusion that the lifts are flat objects.

## Main results

* `AlgebraicGeometry.Stack.isParasitic_of_isFlat_isLfp_jointlySurjective`: **Stacks 0774** (4).

## Implementation notes

The hypothesis is phrased with
`AlgebraicGeometry.Stack.modulePresheafPullbackOfHom`, the inverse image of *presheaves* of
modules of clause (1), applied to the underlying presheaf of `ℱ`: that functor is restriction
along the functor the 1-morphism underlies followed by a restriction of scalars, so the sections
of `(f j)^*ℱ` at an object `x` are literally the sections of `ℱ` at `f j (x)` and no comparison
map enters the proof. Sheafifying the inverse image would change nothing about the hypothesis at
a flat object, by clause (2)(a), but it would insert a transport.

The family `{f (a i)(x_i) → y}` is a covering family of the fppf site of `𝒴` (**Stacks 06TP**)
for the two reasons the inherited site of **Stacks 06NU** asks for: every morphism of a category
fibred in groupoids is strongly cartesian, and the family of images generates a covering sieve
downstairs because the underlying morphisms of schemes are flat, locally of finite presentation
and jointly surjective (`AlgebraicGeometry.mem_topology_of_family`). The images differ from
`W_i → U` by the `CategoryTheory.eqToHom` of `CategoryTheory.Functor.IsHomLift.fac`, which is why
the comparison is a refinement of sieves rather than an equality of families.

## References

* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0774](https://stacks.math.columbia.edu/tag/0774)
* [Stacks Project, Tag 06NU](https://stacks.math.columbia.edu/tag/06NU)
* [Stacks Project, Tag 06PW](https://stacks.math.columbia.edu/tag/06PW)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 07AN](https://stacks.math.columbia.edu/tag/07AN)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u w t v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0774** (4). Let `f j : 𝒳 j ⟶ 𝒴` be a jointly surjective family of flat, locally
finitely presented 1-morphisms of algebraic stacks over `S`, and let `ℱ` be a sheaf of
`𝒪_𝒴`-modules on the fppf site of `𝒴`. If every inverse image `(f j)^*ℱ` is parasitic, then `ℱ`
is parasitic.

At a flat object `y` of `𝒴` the covering of
`AlgebraicGeometry.Stack.exists_fppfCovering_family_flatObject_lift` supplies an fppf covering
family of `y` by objects `f (a i)(x_i)` with `x_i` a *flat* object of `𝒳 (a i)`; the sections of
`ℱ` there are the sections of `(f (a i))^*ℱ` at `x_i`, which vanish, and a sheaf is
separated. -/
@[stacks 0774 "part (4): an fppf sheaf of modules whose inverse images along a jointly surjective
family of flat, locally finitely presented 1-morphisms of algebraic stacks are all parasitic is
parasitic"]
theorem isParasitic_of_isFlat_isLfp_jointlySurjective {J : Type v}
    {𝒳 : J → AlgebraicStacks.{u, w} B S hS} {𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : ∀ j, 𝒳 j ⟶ 𝒴)
    (hflat : ∀ j, AlgebraicStacks.IsFlat B S hS (f j))
    (hlfp : ∀ j, AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (f j))
    (hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒴)) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)))
    (F : SheafOfModules.{t}
      (FibredSite.ringStructureSheafCore B S hS 𝒴.val.val.p
        𝒴.val.isFiberedInGroupoids SiteKind.fppf))
    (hF : ∀ j, IsParasitic B S hS (𝒳 j) SiteKind.fppf
      ((modulePresheafPullbackOfHom.{u, w, t} B S hS (f j) SiteKind.fppf).obj F.val)) :
    IsParasitic B S hS 𝒴 SiteKind.fppf F.val := by
  intro y hy
  obtain ⟨I, W, m, a, hmflat, hmlfp, hmsurj, hlift⟩ :=
    exists_fppfCovering_family_flatObject_lift.{u, w, v} B S hS f hflat hlfp hjs
      (𝒴.val.val.p.obj y) ⟨y, rfl⟩ hy
  choose x hxflat α hα using hlift
  have hcov : Sieve.generate (Presieve.ofArrows
      (fun i => (CatFiberedInGroupoids.homFunctor (f (a i)).hom).obj (x i)) α) ∈
      BigFppfOver.associatedTopology B S hS 𝒴.val.val.p SiteKind.fppf y := by
    apply Precoverage.generate_mem_toGrothendieck
    refine ⟨fun _ k _ => 𝒴.val.isFiberedInGroupoids.isStronglyCartesian k, ?_⟩
    rw [GrothendieckTopology.mem_toPrecoverage_iff]
    refine (BigFppfOver.topology B S hS).superset_covering ?_
      (mem_topology_of_family B S hS W m hmflat hmlfp hmsurj)
    intro V k hk
    obtain ⟨T, h, g, ⟨i⟩, rfl⟩ := hk
    have hαi := hα i
    refine Sieve.downward_closed _ ?_ h
    refine ⟨𝒴.val.val.p.obj ((CatFiberedInGroupoids.homFunctor (f (a i)).hom).obj (x i)),
      eqToHom (IsHomLift.domain_eq 𝒴.val.val.p
        (Over.homMk (m i) rfl :
          (Over.mk (m i ≫ (𝒴.val.val.p.obj y).hom) : BigFppfOver B S hS) ⟶
            𝒴.val.val.p.obj y) (α i)).symm,
      𝒴.val.val.p.map (α i), Presieve.map_map (Presieve.ofArrows.mk i), ?_⟩
    simpa using (IsHomLift.fac 𝒴.val.val.p
      (Over.homMk (m i) rfl :
        (Over.mk (m i ≫ (𝒴.val.val.p.obj y).hom) : BigFppfOver B S hS) ⟶
          𝒴.val.val.p.obj y) (α i)).symm
  have key : ∀ s : F.val.obj (op y), s = 0 := by
    intro s
    refine Stacks.SheafOfModules.eq_zero_of_locally_eq_zero s hcov ?_
    rintro Y g ⟨Z, h, k, ⟨i⟩, rfl⟩
    have hzero : F.val.map (α i).op s = 0 := (hF (a i) (x i) (hxflat i)).elim _ 0
    change F.val.map ((α i).op ≫ h.op) s = 0
    rw [PresheafOfModules.map_comp_apply, hzero]
    exact map_zero _
  exact ⟨fun c d => (key c).trans (key d).symm⟩

end AlgebraicGeometry.Stack

end
