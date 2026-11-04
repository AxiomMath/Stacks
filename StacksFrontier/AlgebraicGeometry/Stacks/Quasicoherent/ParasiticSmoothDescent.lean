module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmoothEtaleRefinementRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.JointlySurjectiveSmoothEtaleLocalLifts
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticFlatLocalLifts
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.EtaleLocalLifts

/-!
# Parasitic descends along a jointly surjective smooth family (Stacks 0774)

Let `f j : 𝒳 j ⟶ 𝒴`, `j ∈ J`, be a family of *smooth* 1-morphisms of algebraic stacks over `S`
(**Stacks 075U**) which is jointly surjective, that is `|𝒴| = ⋃ j |f j|(|𝒳 j|)`. Clause (3) of
**Stacks 0774** says that a sheaf of `𝒪_𝒴`-modules on the *étale* site of `𝒴` is parasitic
(**Stacks 0773**) as soon as every inverse image `(f j)^*ℱ` is.

This is the source's proof. Let `y` be an object of `𝒴` lying over a scheme `U` with
`y : U → 𝒴` flat, and let `s` be a section of `ℱ` at `y`.

* For every point of `U`, the 2-fibre product `𝒳 j ×_𝒴 U` for a suitable `j` has a point above
  it, and a smooth surjective scheme presentation of that 2-fibre product gives a *smooth*
  morphism `m : T → U` hitting the point together with a lift `x` of `y` to `𝒳 j` over `T`. That
  lift is a **flat object** of `𝒳 j`, because it is the image of the tautological object under a
  smooth morphism followed by the base change of the flat `y : U → 𝒴`; this is
  `AlgebraicGeometry.Stack.exists_flatObject_lift_of_isSmooth_at_point` below. Hence
  `(f j)^*ℱ` vanishes at `x`, i.e. `ℱ` vanishes at `f j (x)`, and so `s` restricts to zero along
  the comparison morphism `f j (x) ⟶ y`.
* The smooth covering so obtained is refined by an **étale** one: a smooth morphism of the site
  admits, above any point of its image, an étale morphism factoring through it
  (`AlgebraicGeometry.Space.exists_etale_site_factorisation_of_smooth`, the site form of
  **Stacks 055U**). This is the source's "the smooth topology is the same as the étale topology,
  so refine the covering by an étale one".
* Restricting the comparison morphism along such a factorisation — a cartesian lift in the
  category fibred in groupoids — produces, for every point of `U`, an étale morphism to `U` and a
  morphism to `y` over it along which `s` still restricts to zero. The resulting family is an
  étale covering of `y`, and `ℱ` is an étale sheaf, so `s = 0`.

## Main results

* `AlgebraicGeometry.Stack.exists_flatObject_lift_of_isSmooth_at_point`: the smooth analogue of
  `AlgebraicGeometry.Stack.exists_flatObject_lift_of_isFlat_isLfp_at_point` — a flat object lifts
  along a smooth morphism of the site, through a prescribed point, to a *flat object*.
* `AlgebraicGeometry.Stack.isParasitic_of_isSmooth_jointlySurjective`: **Stacks 0774** (3).

## Implementation notes

The lift produced by the second step is *not* claimed to be a flat object, and it need not be: the
factorising morphism of the étale refinement is not flat. It does not have to be, because the
vanishing of `s` is transported from the smooth level — `s` restricted along `f j (x) ⟶ y`
already vanishes, and the étale member factors through that morphism, so the restriction along
the étale member is a restriction of zero. This is why clause (3) needs no étale analogue of
`AlgebraicGeometry.Stack.exists_fppfCovering_family_flatObject_lift`, and it is also what the
source's "the injection `ℱ(x) → ∏ ℱ(x'_j)` factors through a zero map" says.

As in clause (4), the hypothesis is phrased with the inverse image of *presheaves* of modules,
`AlgebraicGeometry.Stack.modulePresheafPullbackOfHom`, whose sections at an object `x` are
literally the sections of `ℱ` at `f j (x)`.

## References

* [Stacks Project, Tag 055U](https://stacks.math.columbia.edu/tag/055U)
* [Stacks Project, Tag 055V](https://stacks.math.columbia.edu/tag/055V)
* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0774](https://stacks.math.columbia.edu/tag/0774)
* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
* [Stacks Project, Tag 075W](https://stacks.math.columbia.edu/tag/075W)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u w t v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A smooth morphism of the site through a prescribed point, along which a flat object lifts
to a flat object.**

This is `AlgebraicGeometry.Stack.exists_scheme_lift_of_isSmooth_at_point` with the extra
hypothesis that `y` is a flat object of `𝒴` and the extra conclusion that the lift is a flat
object of `𝒳`: the lift is the image of the tautological object under the composite of a smooth
surjective scheme presentation of the 2-fibre product `𝒳 ×_𝒴 U` with the projection to `𝒳`, and
that projection is the base change of the 2-Yoneda 1-morphism of `y`, which is flat exactly
because `y` is a flat object. -/
theorem exists_flatObject_lift_of_isSmooth_at_point
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hsm : AlgebraicStacks.IsSmooth B S hS f)
    (U : BigFppfOver B S hS) (y : 𝒴.val.val.p.Fiber U)
    (hy : flatObject B S hS 𝒴.val y.1)
    (z : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS U))
    (hz : AlgebraicStacks.pointsMap B S hS (fibreObjectStackMap B S hS 𝒴 U y) z ∈
      Set.range (AlgebraicStacks.pointsMap B S hS f)) :
    ∃ (T : B.Schemes) (m : T ⟶ U.left), Smooth (B.inclusion.map m) ∧
      pointsHomeomorphScheme B S hS U z ∈ Set.range (B.inclusion.map m) ∧
      ∃ x : 𝒳.val.val.obj, flatObject B S hS 𝒳.val x ∧
        ∃ α : (CatFiberedInGroupoids.homFunctor f.hom).obj x ⟶ y.1,
          𝒴.val.val.p.IsHomLift
            (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U) α := by
  classical
  obtain ⟨y, rfl⟩ := y
  let b : schemeStack.{u, w} B S hS (𝒴.val.val.p.obj y) ⟶ 𝒴 :=
    fibreObjectStackMap B S hS 𝒴 (𝒴.val.val.p.obj y) (Functor.Fiber.mk rfl)
  let Y : schemeFibredCategory B S hS (𝒴.val.val.p.obj y) ⟶ 𝒴.val := b.hom
  have hb : AlgebraicStacks.IsFlat B S hS b := isFlat_fibreObjectStackMap B S hS y hy
  let P : Bicategory.TwoCommSq b f := twoFibreProductSquareAlgebraicStacks B S hS b f
  have hP : Bicategory.IsTwoFibreProduct P :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS b f
  have hPsm : AlgebraicStacks.IsSmooth B S hS P.fst :=
    AlgebraicStacks.isSmooth_baseChange B S hS f b P hP hsm
  have hPsnd : AlgebraicStacks.IsFlat B S hS P.snd :=
    AlgebraicStacks.isFlat_baseChange B S hS b f P.swap
      (Bicategory.isTwoFibreProduct_swap hP) hb
  obtain ⟨V, c, hcsm, hcsurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS P.pt
  have hwsm : AlgebraicStacks.IsSmooth B S hS (c ≫ P.fst) :=
    AlgebraicStacks.isSmooth_comp B S hS c P.fst hcsm hPsm
  have hsndflat : AlgebraicStacks.IsFlat B S hS (c ≫ P.snd) :=
    AlgebraicStacks.isFlat_comp B S hS c P.snd
      (AlgebraicStacks.isFlat_of_isSmooth B S hS c hcsm) hPsnd
  obtain ⟨q, hqsm, ⟨e⟩⟩ := exists_schemeMap_of_isSmooth B S hS (c ≫ P.fst) hwsm
  obtain ⟨ξ, hξ⟩ := hz
  obtain ⟨pt, hpt, -⟩ :=
    exists_point_of_isTwoFibreProduct_algebraicStacks B S hS P hP z ξ hξ.symm
  obtain ⟨tt, ht⟩ := hcsurj pt
  have htz : AlgebraicStacks.pointsMap B S hS (c ≫ P.fst) tt = z := by
    rwa [AlgebraicStacks.pointsMap_comp, Function.comp_apply, ht]
  have hpts : AlgebraicStacks.pointsMap B S hS (c ≫ P.fst) =
      pointsMap B S hS (schemeFibredCategory B S hS V).val
        (Classical.choose (schemeStack.{u, w} B S hS V).property)
        (Classical.choose (schemeStack.{u, w} B S hS (𝒴.val.val.p.obj y)).property)
        (schemeFibredCategoryMap B S hS q).hom :=
    pointsMap_eq_of_basedNatTrans B S hS (schemeFibredCategory B S hS V).val _ _ e.hom.hom
  refine ⟨V.left, q.left, hqsm, ⟨pointsHomeomorphScheme B S hS V tt, ?_⟩, ?_⟩
  · calc B.inclusion.map q.left (pointsHomeomorphScheme B S hS V tt)
        = pointsHomeomorphScheme B S hS (𝒴.val.val.p.obj y)
            (pointsMap B S hS (schemeFibredCategory B S hS V).val
              (schemeFibredCategory B S hS V).property
              (schemeFibredCategory B S hS (𝒴.val.val.p.obj y)).property
              (schemeFibredCategoryMap B S hS q).hom tt) :=
          (pointsHomeomorphScheme_naturality B S hS q tt).symm
      _ = pointsHomeomorphScheme B S hS (𝒴.val.val.p.obj y)
            (AlgebraicStacks.pointsMap B S hS (c ≫ P.fst) tt) :=
          congrArg (pointsHomeomorphScheme B S hS (𝒴.val.val.p.obj y)) (congrFun hpts tt).symm
      _ = pointsHomeomorphScheme B S hS (𝒴.val.val.p.obj y) z :=
          congrArg (pointsHomeomorphScheme B S hS (𝒴.val.val.p.obj y)) htz
  refine ⟨(c ≫ P.snd).hom.hom.obj (Over.mk (𝟙 V)), FlatFppf.flatObject_map B S hS (c ≫ P.snd)
    hsndflat ⟨Over.mk (𝟙 V), flatObject_schemeStack_id.{u, w} B S hS V⟩, ?_⟩
  obtain ⟨α, hα⟩ := exists_isHomLift_twoCellFibreLift 𝒳.val.val.p 𝒴.val.val.p
    (Functor.Fiber.mk (a := y) rfl) q f.hom.hom (c ≫ P.snd).hom.hom
    (Functor.TwoYoneda.liftBased 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
      (𝒴.val.val.p.obj y) (Functor.Fiber.mk rfl))
    (Functor.TwoYoneda.chosenLift 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
      (𝒴.val.val.p.obj y) (Functor.Fiber.mk rfl)
      (Over.mk (𝟙 (𝒴.val.val.p.obj y)))).φ
    ((Functor.TwoYoneda.chosenLift 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
      (𝒴.val.val.p.obj y) (Functor.Fiber.mk rfl)
      (Over.mk (𝟙 (𝒴.val.val.p.obj y)))).isStronglyCartesian.toIsHomLift)
    ((Bicategory.whiskerLeft c P.iso.inv).hom.hom ≫
      (Bicategory.whiskerRight e.hom Y).hom)
  exact ⟨α, isHomLift_homMk_left B S hS 𝒴.val.val.p q α hα⟩

/-- The morphism `Over.mk (e ≫ U.hom) ⟶ U` of the big site given by `e`. -/
private abbrev overHomMk {U : BigFppfOver B S hS} {W : B.Schemes} (e : W ⟶ U.left) :
    (Over.mk (e ≫ U.hom) : BigFppfOver B S hS) ⟶ U := Over.homMk e rfl

/-- **Stacks 0774** (3). Let `f j : 𝒳 j ⟶ 𝒴` be a jointly surjective family of smooth
1-morphisms of algebraic stacks over `S`, and let `ℱ` be a sheaf of `𝒪_𝒴`-modules on the étale
site of `𝒴`. If every inverse image `(f j)^*ℱ` is parasitic, then `ℱ` is parasitic.

At a flat object `y` of `𝒴`, every point of the scheme `y` lies over is hit by a smooth morphism
`m` of the site carrying a lift of `y` to some `𝒳 j` which is a *flat* object there
(`AlgebraicGeometry.Stack.exists_flatObject_lift_of_isSmooth_at_point`), so the sections of `ℱ`
restrict to zero along the comparison morphism. Refining `m` by an étale morphism factoring
through it (**Stacks 055U**) and taking a cartesian lift of the comparison morphism gives an
*étale* covering family of `y` along every member of which the sections of `ℱ` restrict to zero;
`ℱ` is an étale sheaf, hence separated, so they vanish. -/
@[stacks 0774 "part (3): an étale sheaf of modules whose inverse images along a jointly surjective
family of smooth 1-morphisms of algebraic stacks are all parasitic is parasitic"]
theorem isParasitic_of_isSmooth_jointlySurjective {J : Type v}
    {𝒳 : J → AlgebraicStacks.{u, w} B S hS} {𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : ∀ j, 𝒳 j ⟶ 𝒴)
    (hsmooth : ∀ j, AlgebraicStacks.IsSmooth B S hS (f j))
    (hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒴)) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)))
    (F : SheafOfModules.{t}
      (FibredSite.ringStructureSheafCore B S hS 𝒴.val.val.p
        𝒴.val.isFiberedInGroupoids SiteKind.etale))
    (hF : ∀ j, IsParasitic B S hS (𝒳 j) SiteKind.etale
      ((modulePresheafPullbackOfHom.{u, w, t} B S hS (f j) SiteKind.etale).obj F.val)) :
    IsParasitic B S hS 𝒴 SiteKind.etale F.val := by
  classical
  intro y hy
  have hcomp : ∀ {a b : 𝒴.val.val.obj} (ρ : a ⟶ b) (α : b ⟶ y) (s : F.val.obj (op y)),
      F.val.map α.op s = 0 → F.val.map (ρ ≫ α).op s = 0 := fun ρ α s h => by
    rw [op_comp, PresheafOfModules.map_comp_apply, h]
    exact map_zero _
  have key : ∀ pt : B.inclusion.obj (𝒴.val.val.p.obj y).left,
      ∃ (W : B.Schemes) (e : W ⟶ (𝒴.val.val.p.obj y).left),
        Etale (B.inclusion.map e) ∧ pt ∈ Set.range (B.inclusion.map e) ∧
          ∃ (z : 𝒴.val.val.obj) (β : z ⟶ y),
            𝒴.val.val.p.IsHomLift
              (overHomMk B S hS e) β ∧
              ∀ s : F.val.obj (op y), F.val.map β.op s = 0 := by
    intro pt
    let _ := pointTopology B S hS (schemeFibredCategory B S hS (𝒴.val.val.p.obj y))
    let z : AlgebraicStacks.points B S hS
        (schemeStack.{u, w} B S hS (𝒴.val.val.p.obj y)) :=
      (pointsHomeomorphScheme B S hS (𝒴.val.val.p.obj y)).symm pt
    have hmem : AlgebraicStacks.pointsMap B S hS
        (fibreObjectStackMap B S hS 𝒴 (𝒴.val.val.p.obj y) ⟨y, rfl⟩) z ∈
        ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)) := by
      rw [← hjs]
      exact Set.mem_univ _
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hmem
    obtain ⟨T, m, hmsm, hmhit, x, hxflat, α, hα⟩ :=
      exists_flatObject_lift_of_isSmooth_at_point B S hS (f j) (hsmooth j)
        (𝒴.val.val.p.obj y) ⟨y, rfl⟩ hy z hj
    rw [show pointsHomeomorphScheme B S hS (𝒴.val.val.p.obj y) z = pt from
      (pointsHomeomorphScheme B S hS (𝒴.val.val.p.obj y)).apply_symm_apply pt] at hmhit
    obtain ⟨R, c, hce, hcpt⟩ := Space.exists_etale_site_factorisation_of_smooth B S hS
      (overHomMk B S hS m) hmsm pt hmhit
    have hxbase : 𝒴.val.val.p.obj ((CatFiberedInGroupoids.homFunctor (f j).hom).obj x) =
        Over.mk (m ≫ (𝒴.val.val.p.obj y).hom) :=
      IsHomLift.domain_eq 𝒴.val.val.p
        (overHomMk B S hS m) α
    obtain ⟨z', ρ, hρ⟩ := 𝒴.val.isFiberedInGroupoids.exists_lift c
      ((CatFiberedInGroupoids.homFunctor (f j).hom).obj x) hxbase
    refine ⟨R.left,
      (c ≫ (overHomMk B S hS m)).left, hce, hcpt, z', ρ ≫ α, ?_, ?_⟩
    · exact isHomLift_homMk_left B S hS 𝒴.val.val.p _ (ρ ≫ α)
        (IsHomLift.comp 𝒴.val.val.p c _ ρ α)
    · intro s
      exact hcomp ρ α s ((hF j x hxflat).elim _ 0)
  choose WW₀ ee₀ hetale₀ hhit₀ zz₀ ββ₀ hβ₀ hvan₀ using key
  obtain ⟨I, WW, ee, zz, ββ, hetale, hhit, hβ, hvan⟩ :
      ∃ (I : Type (u + 1)) (W : I → B.Schemes)
        (e : ∀ i, W i ⟶ (𝒴.val.val.p.obj y).left) (z : I → 𝒴.val.val.obj)
        (β : ∀ i, z i ⟶ y),
        (∀ i, Etale (B.inclusion.map (e i))) ∧
          (∀ pt : B.inclusion.obj (𝒴.val.val.p.obj y).left,
              ∃ i, pt ∈ Set.range (B.inclusion.map (e i))) ∧
            (∀ i, 𝒴.val.val.p.IsHomLift
                (Over.homMk (e i) rfl :
                  (Over.mk (e i ≫ (𝒴.val.val.p.obj y).hom) : BigFppfOver B S hS) ⟶
                    𝒴.val.val.p.obj y) (β i)) ∧
              ∀ (i) (s : F.val.obj (op y)), F.val.map (β i).op s = 0 :=
    ⟨ULift.{u + 1} (B.inclusion.obj (𝒴.val.val.p.obj y).left),
      fun i => WW₀ i.down, fun i => ee₀ i.down, fun i => zz₀ i.down, fun i => ββ₀ i.down,
      fun i => hetale₀ i.down, fun pt => ⟨ULift.up pt, hhit₀ pt⟩,
      fun i => hβ₀ i.down, fun i => hvan₀ i.down⟩
  have hcov : Sieve.generate (Presieve.ofArrows zz ββ) ∈
      BigFppfOver.associatedTopology B S hS 𝒴.val.val.p SiteKind.etale y := by
    apply Precoverage.generate_mem_toGrothendieck
    refine ⟨fun _ k _ => 𝒴.val.isFiberedInGroupoids.isStronglyCartesian k, ?_⟩
    rw [GrothendieckTopology.mem_toPrecoverage_iff]
    refine (BigFppfOver.baseOverTopology B S hS SiteKind.etale).superset_covering ?_
      (mem_etaleOverTopology_of_family B S hS WW ee hetale hhit)
    intro Vv k hk
    obtain ⟨T, h, g, ⟨i⟩, rfl⟩ := hk
    have := hβ i
    refine Sieve.downward_closed _ ?_ h
    refine ⟨𝒴.val.val.p.obj (zz i),
      eqToHom (IsHomLift.domain_eq 𝒴.val.val.p
        (Over.homMk (ee i) rfl :
          (Over.mk (ee i ≫ (𝒴.val.val.p.obj y).hom) : BigFppfOver B S hS) ⟶
            𝒴.val.val.p.obj y) (ββ i)).symm,
      𝒴.val.val.p.map (ββ i), Presieve.map_map (Presieve.ofArrows.mk i), ?_⟩
    simpa using (IsHomLift.fac 𝒴.val.val.p
      (Over.homMk (ee i) rfl :
        (Over.mk (ee i ≫ (𝒴.val.val.p.obj y).hom) : BigFppfOver B S hS) ⟶
          𝒴.val.val.p.obj y) (ββ i)).symm
  have hzero : ∀ s : F.val.obj (op y), s = 0 := by
    intro s
    refine Stacks.SheafOfModules.eq_zero_of_locally_eq_zero s hcov ?_
    rintro Y g ⟨Z, h, k, ⟨i⟩, rfl⟩
    exact hcomp h _ s (hvan i s)
  exact ⟨fun cc dd => (hzero cc).trans (hzero dd).symm⟩

end AlgebraicGeometry.Stack

end
