module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleCover
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategory
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSiteEquivalence

/-!
# Points of algebraic spaces factor locally through affine étale charts

Let `F` be an algebraic space over a scheme `S` of a big fppf site and let `a` be a point of `F`
with values in an object `V` of the big fppf site.  Locally on `V` for the fppf topology, the
point `a` is the restriction of the tautological point of an *affine* étale chart of `F`, along a
morphism from an *affine* object.

For a pair of morphisms `s, t : R ⟶ U` of algebraic spaces and two étale charts `W₁, W₂` of `U`, a
point `r` of `R` whose images under `s` and `t` factor through `W₁` and `W₂` locally factors
through an affine étale chart `V` of `R` which is the source of commutative squares of charts over
`s` to `W₁` and over `t` to `W₂`.

## Main definitions

* `AlgebraicGeometry.Space.affineChartPresieve`: the affine objects over which a point factors
  through an affine étale chart.
* `AlgebraicGeometry.Space.twoChartPresieve`: the affine objects over which a point of `R`
  factors through an affine étale chart carrying chart squares over `s` and over `t`.

## Main results

* `AlgebraicGeometry.BigFppfOver.generate_affine_mem`: the affine members of a covering sieve of
  the big fppf site generate a covering sieve.
* `AlgebraicGeometry.Space.generate_affineChartPresieve_mem` and
  `AlgebraicGeometry.Space.generate_twoChartPresieve_mem`: both presieves generate covering
  sieves for the fppf topology.

## References

* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The arrows with affine source of a covering sieve of the big fppf site generate a covering
sieve. -/
theorem generate_affine_mem {V : BigFppfOver B S hS} {Q : Sieve V} (hQ : Q ∈ topology B S hS V) :
    Sieve.generate (fun V' (e : V' ⟶ V) => Q e ∧ IsAffineOver B S hS V') ∈
      topology B S hS V := by
  choose I W π hW _ hcov _ using fun (Y : BigFppfOver B S hS) =>
    exists_affine_open_cover' B S hS Y
  refine (topology B S hS).superset_covering ?_
    ((topology B S hS).bind_covering (R := fun Y _ _ => Sieve.ofArrows (W Y) (π Y)) hQ
      (fun Y _ _ => hcov Y))
  intro Z f hf
  obtain ⟨Y, g, h, hg, hh, hfac⟩ := hf
  obtain ⟨i, k, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hh
  refine ⟨_, k, π Y i ≫ h, ⟨Q.downward_closed hg _, hW Y i⟩, ?_⟩
  rw [← hfac, Category.assoc]

end AlgebraicGeometry.BigFppfOver

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The presieve of affine objects over which a point of an algebraic space factors through an
affine étale chart. -/
def affineChartPresieve (F : AlgebraicSpaces B S hS) {V : BigFppfOver B S hS}
    (a : F.1.obj (op V)) : Presieve V :=
  fun V' h => IsAffineOver B S hS V' ∧ ∃ (W : SmallEtale B S hS F.1)
    (_ : IsAffineOver B S hS ((SmallEtale.toOver B S hS F.1).obj W))
    (g : V' ⟶ (SmallEtale.toOver B S hS F.1).obj W),
    F.1.map h.op a = F.1.map g.op (yonedaEquiv W.obj.hom)

/-- If a covering sieve `Q` is such that, for each `f ∈ Q`, the affine arrows into the source of
`f` whose composite with `f` lies in `P` generate a covering sieve, then `P` generates a covering
sieve. -/
private theorem generate_mem_of_bind_affine {V : BigFppfOver B S hS} {Q : Sieve V}
    (hQ : Q ∈ BigFppfOver.topology B S hS V) (P : Presieve V)
    (h : ∀ ⦃Y⦄ ⦃f : Y ⟶ V⦄, Q f → Sieve.generate (fun V' (e : V' ⟶ Y) =>
      IsAffineOver B S hS V' ∧ P (e ≫ f)) ∈ BigFppfOver.topology B S hS Y) :
    Sieve.generate P ∈ BigFppfOver.topology B S hS V := by
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    ((BigFppfOver.topology B S hS).bind_covering
      (R := fun Y f hf => Sieve.generate (fun V' (e : V' ⟶ Y) =>
        IsAffineOver B S hS V' ∧ P (e ≫ f))) hQ h)
  intro Z f hf
  obtain ⟨Y, g, h, _hg, hh, hfac⟩ := hf
  obtain ⟨Z', k, e, ⟨_, he⟩, hkfac⟩ := hh
  exact ⟨_, k, e ≫ h, he, by rw [← hfac, ← hkfac, Category.assoc]⟩

/-- A point of an algebraic space factors fppf locally through affine étale charts: the affine
objects over which the point factors through an affine étale chart generate a covering sieve. -/
theorem generate_affineChartPresieve_mem (F : AlgebraicSpaces B S hS) {V : BigFppfOver B S hS}
    (a : F.1.obj (op V)) :
    Sieve.generate (affineChartPresieve B S hS F a) ∈ BigFppfOver.topology B S hS V := by
  let 𝒰 := (Stack.fibredCategory B S hS F.1).val
  have h𝒰 : 𝒰.p.IsFiberedInGroupoids := (Stack.fibredCategory B S hS F.1).property
  let y : 𝒰.obj := ⟨V, Discrete.mk a⟩
  have hcov := restrictionFunctor_coversTop B S hS F.1 𝒰.p F.2 h𝒰
    (StacksRepresentableCFG.EquivalenceOver.refl _) y
  have hpush := (Functor.mem_inheritedTopology_iff_functorPushforward 𝒰.p
    (BigFppfOver.baseOverTopology B S hS .etale) h𝒰 _).1 hcov
  have hpush' := BigFppfOver.baseOverTopology_le_fppf B S hS .etale _ hpush
  refine generate_mem_of_bind_affine B S hS hpush' _ ?_
  intro Y f hf
  obtain ⟨Z, g, h, ⟨A, ⟨b⟩⟩, rfl⟩ := hf
  have hga : Z.fiber.as = F.1.map g.base.op a := Discrete.eq_of_hom g.fiber
  have hba : Z.fiber.as = F.1.map b.base.op (yonedaEquiv A.obj.hom) := Discrete.eq_of_hom b.fiber
  obtain ⟨J, W, π, hW, hπ, hcovA, -⟩ := BigFppfOver.exists_affine_open_cover' B S hS
    ((SmallEtale.toOver B S hS F.1).obj A)
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    (BigFppfOver.generate_affine_mem B S hS
      ((BigFppfOver.topology B S hS).pullback_stable (h ≫ b.base)
        (show Sieve.ofArrows W π ∈ _ from hcovA)))
  rintro V'' e ⟨V₃, e₁, e₂, ⟨he₂, hV₃⟩, rfl⟩
  obtain ⟨j, k, hk⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 he₂
  refine ⟨V₃, e₁, e₂, ⟨hV₃, ?_⟩, rfl⟩
  have hj : IsEtaleChart B S hS F.1 (CostructuredArrow.mk (yoneda.map (π j) ≫ A.obj.hom)) := by
    have := hπ j
    exact etale_comp_of_scheme B S hS (π j) A.obj.hom inferInstance A.property
  refine ⟨hV₃, ⟨_, hj⟩, hW j, k, ?_⟩
  have key : F.1.map (h ≫ g.base).op a = F.1.map (h ≫ b.base).op (yonedaEquiv A.obj.hom) := by
    have e1 := Functor.map_comp_apply F.1 g.base.op h.op a
    have e2 := Functor.map_comp_apply F.1 b.base.op h.op (yonedaEquiv A.obj.hom)
    refine e1.trans (Eq.trans ?_ e2.symm)
    exact congrArg _ (hga.symm.trans hba)
  show F.1.map (e₂ ≫ h ≫ g.base).op a =
    F.1.map k.op (yonedaEquiv (yoneda.map (π j) ≫ A.obj.hom))
  rw [← yonedaEquiv_naturality]
  refine (Functor.map_comp_apply F.1 (h ≫ g.base).op e₂.op a).trans ?_
  rw [key]
  refine (Functor.map_comp_apply F.1 (h ≫ b.base).op e₂.op _).symm.trans ?_
  refine Eq.trans ?_ (Functor.map_comp_apply F.1 (π j).op k.op _)
  show F.1.map (e₂ ≫ h ≫ b.base).op _ = F.1.map (k ≫ π j).op _
  rw [hk]; rfl

/-- The presieve of affine objects over which a point of an algebraic space `R` with a map to
`U` along two morphisms factors through an affine chart with two chart diagrams. -/
def twoChartPresieve {R U : AlgebraicSpaces B S hS} (s t : R ⟶ U) {T : BigFppfOver B S hS}
    (r : R.1.obj (op T)) (W₁ W₂ : SmallEtale B S hS U.1)
    (g₁ : T ⟶ (SmallEtale.toOver B S hS U.1).obj W₁)
    (g₂ : T ⟶ (SmallEtale.toOver B S hS U.1).obj W₂) : Presieve T :=
  fun T' h => IsAffineOver B S hS T' ∧ ∃ (V : SmallEtale B S hS R.1)
    (_ : IsAffineOver B S hS ((SmallEtale.toOver B S hS R.1).obj V))
    (k : T' ⟶ (SmallEtale.toOver B S hS R.1).obj V)
    (ds : (SmallEtale.toOver B S hS R.1).obj V ⟶ (SmallEtale.toOver B S hS U.1).obj W₁)
    (dt : (SmallEtale.toOver B S hS R.1).obj V ⟶ (SmallEtale.toOver B S hS U.1).obj W₂),
    V.obj.hom ≫ s.hom = yoneda.map ds ≫ W₁.obj.hom ∧
    V.obj.hom ≫ t.hom = yoneda.map dt ≫ W₂.obj.hom ∧
    R.1.map h.op r = R.1.map k.op (yonedaEquiv V.obj.hom) ∧
    h ≫ g₁ = k ≫ ds ∧ h ≫ g₂ = k ≫ dt

/-- If a point `r` of `R` maps under `s` to the pullback of the point `w` along `g`, and agrees
after restriction with the pullback of the point `ι`, then the two composites into `U` agree. -/
private theorem yoneda_map_comp_eq_of_app_eq {R U : AlgebraicSpaces B S hS} (s : R ⟶ U)
    {T T' X Y : BigFppfOver B S hS} (r : R.1.obj (op T)) (x : T' ⟶ T) (g : T ⟶ Y) (m : T' ⟶ X)
    (w : yoneda.obj Y ⟶ U.1) (ι : yoneda.obj X ⟶ R.1)
    (hs : s.hom.app _ r = U.1.map g.op (yonedaEquiv w))
    (hR : R.1.map x.op r = R.1.map m.op (yonedaEquiv ι)) :
    yoneda.map (x ≫ g) ≫ w = yoneda.map m ≫ ι ≫ s.hom := by
  apply yonedaEquiv.injective
  rw [← yonedaEquiv_naturality, ← yonedaEquiv_naturality, yonedaEquiv_comp,
    op_comp, Functor.map_comp_apply, ← hs,
    ← NatTrans.naturality_apply, hR, NatTrans.naturality_apply]

/-- A point of `R` whose images under `s` and `t` factor through the charts `W₁` and `W₂` factors
fppf locally through affine étale charts of `R` carrying chart squares over `s` and `t`. -/
theorem generate_twoChartPresieve_mem {R U : AlgebraicSpaces B S hS} (s t : R ⟶ U)
    {T : BigFppfOver B S hS} (r : R.1.obj (op T)) (W₁ W₂ : SmallEtale B S hS U.1)
    (g₁ : T ⟶ (SmallEtale.toOver B S hS U.1).obj W₁)
    (g₂ : T ⟶ (SmallEtale.toOver B S hS U.1).obj W₂)
    (hs : s.hom.app _ r = U.1.map g₁.op (yonedaEquiv W₁.obj.hom))
    (ht : t.hom.app _ r = U.1.map g₂.op (yonedaEquiv W₂.obj.hom)) :
    Sieve.generate (twoChartPresieve B S hS s t r W₁ W₂ g₁ g₂) ∈ BigFppfOver.topology B S hS T := by
  refine generate_mem_of_bind_affine B S hS (generate_affineChartPresieve_mem B S hS R r) _ ?_
  intro Y f hf
  obtain ⟨T₀, e₀, h₀, ⟨_, V₀, _, k₀, hk₀⟩, rfl⟩ := hf
  let ι₀ := V₀.obj.hom
  let rep₁ := W₁.property.rep
  let gs := ι₀ ≫ s.hom
  let V₁ := rep₁.pullback gs
  let snd₁ := rep₁.snd gs
  let fst₁ := rep₁.fst' gs
  have w₁ : yoneda.map fst₁ ≫ W₁.obj.hom = yoneda.map snd₁ ≫ gs := by
    rw [Functor.relativelyRepresentable.map_fst']; exact rep₁.w gs
  let ι₁ := yoneda.map snd₁ ≫ ι₀
  have hι₁ : IsEtaleChart B S hS R.1 (CostructuredArrow.mk ι₁) :=
    etale_comp_of_scheme B S hS snd₁ ι₀ (W₁.property.property_snd gs) V₀.property
  let rep₂ := W₂.property.rep
  let gt := ι₁ ≫ t.hom
  let V₂ := rep₂.pullback gt
  let snd₂ := rep₂.snd gt
  let fst₂ := rep₂.fst' gt
  have w₂ : yoneda.map fst₂ ≫ W₂.obj.hom = yoneda.map snd₂ ≫ gt := by
    rw [Functor.relativelyRepresentable.map_fst']; exact rep₂.w gt
  let ι₂ := yoneda.map snd₂ ≫ ι₁
  have hι₂ : IsEtaleChart B S hS R.1 (CostructuredArrow.mk ι₂) :=
    etale_comp_of_scheme B S hS snd₂ ι₁ (W₂.property.property_snd gt) hι₁
  have hR₀ : R.1.map (e₀ ≫ h₀).op r = R.1.map (e₀ ≫ k₀).op (yonedaEquiv ι₀) := by
    rw [op_comp, Functor.map_comp_apply, hk₀, ← Functor.map_comp_apply,
      ← op_comp]
  have hl₁ : yoneda.map (e₀ ≫ h₀ ≫ g₁) ≫ W₁.obj.hom = yoneda.map (e₀ ≫ k₀) ≫ gs := by
    set_option synthInstance.maxHeartbeats 400000 in
    simpa using yoneda_map_comp_eq_of_app_eq B S hS s r (e₀ ≫ h₀) g₁ _ _ ι₀ hs hR₀
  let k₁ := rep₁.lift' (e₀ ≫ h₀ ≫ g₁) (e₀ ≫ k₀) hl₁
  have hk₁f : k₁ ≫ fst₁ = e₀ ≫ h₀ ≫ g₁ := rep₁.lift'_fst _ _ _
  have hk₁s : k₁ ≫ snd₁ = e₀ ≫ k₀ := rep₁.lift'_snd _ _ _
  have hR₁ : R.1.map (e₀ ≫ h₀).op r = R.1.map k₁.op (yonedaEquiv ι₁) := by
    rw [hR₀, ← hk₁s, ← yonedaEquiv_naturality, op_comp, Functor.map_comp_apply]
  have hl₂ : yoneda.map (e₀ ≫ h₀ ≫ g₂) ≫ W₂.obj.hom = yoneda.map k₁ ≫ gt := by
    set_option synthInstance.maxHeartbeats 400000 in
    simpa using yoneda_map_comp_eq_of_app_eq B S hS t r (e₀ ≫ h₀) g₂ _ _ ι₁ ht hR₁
  let k₂ := rep₂.lift' (e₀ ≫ h₀ ≫ g₂) k₁ hl₂
  have hk₂f : k₂ ≫ fst₂ = e₀ ≫ h₀ ≫ g₂ := rep₂.lift'_fst _ _ _
  have hk₂s : k₂ ≫ snd₂ = k₁ := rep₂.lift'_snd _ _ _
  obtain ⟨J, O, π, hO, hπ, hcovO, -⟩ := BigFppfOver.exists_affine_open_cover' B S hS V₂
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    (BigFppfOver.generate_affine_mem B S hS
      ((BigFppfOver.topology B S hS).pullback_stable k₂
        (show Sieve.ofArrows O π ∈ _ from hcovO)))
  rintro T' e ⟨T'', e₁, e₂, ⟨he₂, hT''⟩, rfl⟩
  obtain ⟨j, m, hm⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 he₂
  have hπj : IsEtaleChart B S hS R.1 (CostructuredArrow.mk (yoneda.map (π j) ≫ ι₂)) := by
    have := hπ j
    exact etale_comp_of_scheme B S hS (π j) ι₂ inferInstance hι₂
  refine ⟨T'', e₁, e₂, ⟨hT'', hT'', ⟨_, hπj⟩, hO j, m, π j ≫ snd₂ ≫ fst₁, π j ≫ fst₂,
    ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · have w₁' : yoneda.map snd₁ ≫ ι₀ ≫ s.hom = yoneda.map fst₁ ≫ W₁.obj.hom := w₁.symm
    show (yoneda.map (π j) ≫ yoneda.map snd₂ ≫ yoneda.map snd₁ ≫ ι₀) ≫ s.hom = _
    simp only [Functor.map_comp, Category.assoc]
    rw [w₁']
  · have w₂' : yoneda.map snd₂ ≫ yoneda.map snd₁ ≫ ι₀ ≫ t.hom =
        yoneda.map fst₂ ≫ W₂.obj.hom := by
      rw [w₂]; simp only [gt, ι₁, Category.assoc]
    show (yoneda.map (π j) ≫ yoneda.map snd₂ ≫ yoneda.map snd₁ ≫ ι₀) ≫ t.hom = _
    simp only [Functor.map_comp, Category.assoc]
    rw [w₂']
  · have e1 : yonedaEquiv ι₂ = R.1.map snd₂.op (yonedaEquiv ι₁) :=
      (yonedaEquiv_naturality ι₁ snd₂).symm
    show _ = R.1.map m.op (yonedaEquiv (yoneda.map (π j) ≫ ι₂))
    rw [← yonedaEquiv_naturality ι₂ (π j), e1, op_comp, Functor.map_comp_apply, hR₁,
      ← hk₂s, op_comp, Functor.map_comp_apply, ← Functor.map_comp_apply,
      ← op_comp, hm, op_comp, Functor.map_comp_apply]
  · rw [Category.assoc, Category.assoc, ← hk₁f, ← hk₂s, ← Category.assoc, ← Category.assoc,
      hm]
    simp only [Category.assoc]
  · rw [Category.assoc, Category.assoc, ← hk₂f, ← Category.assoc, hm, Category.assoc]

end AlgebraicGeometry.Space

end
