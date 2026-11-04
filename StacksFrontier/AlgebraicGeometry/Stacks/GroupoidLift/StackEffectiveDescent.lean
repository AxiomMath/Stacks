module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackGroupoid
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.SpaceLift
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Stack

/-!
# Descent of a point of a chart along a faithfully flat finitely presented algebra

Let `𝒳` be a stack in groupoids over the big fppf site, `a : (Sch/U₀) ⟶ 𝒳` a 1-morphism and
`ι : Spec P ⟶ U₀` a chart over the affine object `T'`, `A' = Γ(T', ⊤)`. Let `C'` be a faithfully
flat finitely presented `A'`-algebra. A point `u : P → C'` together with an arrow
`r : ξ (v₀ ∘ u) ⟶ ξ (vₗ ∘ u)` of `𝒳` over `Spec (C' ⊗ C')` whose three pullbacks to
`Spec (C' ⊗ C' ⊗ C')` satisfy the cocycle condition exactly is a descent datum for `ξ u` along
`Spec C' ⟶ Spec A'`. It is effective: there is an object `x'` of `𝒳` over `Spec A'` with a
morphism `ξ u ⟶ x'` over `Spec C' ⟶ Spec A'` intertwining `r`
(`AlgebraicGeometry.Stack.GroupoidLift.StackChart.exists_descent_of_hom`).

This is the descent step of the lifting argument for algebraic stacks: the output of the
second-order step `AlgebraicGeometry.Stack.GroupoidLift.NerveDatum.exists_lift_arrow_cocycle`
is exactly such a pair `(u, r)`.

## Main definitions

* `AlgebraicGeometry.Stack.GroupoidLift.StackChart.descDatum`: the descent datum of `(ξ u, r)`
  along `Spec C' ⟶ Spec A'`.

## Main results

* `AlgebraicGeometry.Stack.GroupoidLift.isPushout_nerve_two`: the triple overlap
  `C' ⊗ C' ⊗ C'` is the pushout of two copies of `C' ⊗ C'` over `C'`.
* `AlgebraicGeometry.Stack.GroupoidLift.StackChart.exists_descent_of_hom`: a point `u` with an
  arrow `r` satisfying the cocycle condition descends to an object over `Spec A'`.
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory Opposite Limits
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe w u

/-- A pushout square remains a pushout square after replacing its four morphisms by equal
ones. -/
theorem isPushout_congr {𝒞 : Type*} [Category 𝒞] {X Y Z W : 𝒞} {f f' : X ⟶ Y} {g g' : X ⟶ Z}
    {i i' : Y ⟶ W} {j j' : Z ⟶ W} (h : IsPushout f g i j) (hf : f = f') (hg : g = g')
    (hi : i = i') (hj : j = j') : IsPushout f' g' i' j' := by
  subst hf hg hi hj
  exact h

/-- The comparison `Restriction.compTo` is the unique morphism over `g` through which the
second restriction factors. -/
theorem Functor.Restriction.compTo_eq' {𝒞 : Type*} {𝒮 : Type*} [Category 𝒞] [Category 𝒮]
    (p : 𝒮 ⥤ 𝒞) {W V U : 𝒞} (g : W ⟶ V) (f : V ⟶ U) {h : W ⟶ U} (hh : h = g ≫ f) {x : 𝒮}
    {hx : p.obj x = U} (xr : Functor.Restriction p f x hx) (xrW : Functor.Restriction p h x hx)
    (m : xrW.pt ⟶ xr.pt) (hl : p.IsHomLift g m) (hm : m ≫ xr.hom = xrW.hom) :
    Functor.Restriction.compTo p g f hh xr xrW = m := by
  have := xr.isCart
  have := hl
  have : p.IsHomLift ((eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm) ≫
      (eqToHom xr.hpt ≫ f ≫ eqToHom hx.symm)) xrW.hom := by
    have e : (eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm) ≫
        (eqToHom xr.hpt ≫ f ≫ eqToHom hx.symm)
        = eqToHom xrW.hpt ≫ h ≫ eqToHom hx.symm := by
      subst hh
      simp
    rw [e]
    exact xrW.isHomLift
  exact (Functor.IsStronglyCartesian.map_uniq p (eqToHom xr.hpt ≫ f ≫ eqToHom hx.symm) xr.hom
    (g := eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm) rfl xrW.hom m hm).symm

/-- To check that `β` restricts `α`, it suffices to exhibit the two comparisons. -/
theorem Functor.isRestrictionOf_of_fac {𝒞 : Type*} {𝒮 : Type*} [Category 𝒞] [Category 𝒮]
    (p : 𝒮 ⥤ 𝒞) {W V Ux Uy : 𝒞} (g : W ⟶ V) {fx : V ⟶ Ux} {fy : V ⟶ Uy} {hx_ : W ⟶ Ux}
    {hy_ : W ⟶ Uy} (hfx : hx_ = g ≫ fx) (hfy : hy_ = g ≫ fy) {x y : 𝒮} {hx : p.obj x = Ux}
    {hy : p.obj y = Uy} (xr : Functor.Restriction p fx x hx) (yr : Functor.Restriction p fy y hy)
    (xrW : Functor.Restriction p hx_ x hx) (yrW : Functor.Restriction p hy_ y hy)
    (α : xr.pt ⟶ yr.pt) (β : xrW.pt ⟶ yrW.pt) (mx : xrW.pt ⟶ xr.pt) (hlx : p.IsHomLift g mx)
    (hmx : mx ≫ xr.hom = xrW.hom) (my : yrW.pt ⟶ yr.pt) (hly : p.IsHomLift g my)
    (hmy : my ≫ yr.hom = yrW.hom) (h : β ≫ my = mx ≫ α) :
    Functor.IsRestrictionOf p g hfx hfy xr yr xrW yrW α β := by
  show β ≫ Functor.Restriction.compTo p g fy hfy yr yrW =
    Functor.Restriction.compTo p g fx hfx xr xrW ≫ α
  rw [Functor.Restriction.compTo_eq' p g fy hfy yr yrW my hly hmy,
    Functor.Restriction.compTo_eq' p g fx hfx xr xrW mx hlx hmx, h]

/-- The arrow of a restriction of `x` along `f` lies over `f`. -/
theorem Functor.isHomLift_of_restriction {𝒞 : Type*} {𝒮 : Type*} [Category 𝒞] [Category 𝒮]
    (p : 𝒮 ⥤ 𝒞) {V U : 𝒞} {f : V ⟶ U} {x : 𝒮} {hx : p.obj x = U}
    (xr : Functor.Restriction p f x hx) : p.IsHomLift f xr.hom :=
  (IsHomLift.lift_comp_eqToHom_iff (p := p) f xr.hom hx.symm).mp
    ((IsHomLift.lift_eqToHom_comp_iff (p := p) _ xr.hom xr.hpt).mp xr.isHomLift)

/-- A morphism in the fibre over `W` lies over the identity of `W`. -/
theorem Functor.isHomLift_id_of_fibreHom {𝒞 : Type*} {𝒮 : Type*} [Category 𝒞] [Category 𝒮]
    (p : 𝒮 ⥤ 𝒞) {W : 𝒞} {x y : 𝒮} {hx : p.obj x = W} {hy : p.obj y = W} {ψ : x ⟶ y}
    (hψ : Functor.FibreHom p x y hx hy ψ) : p.IsHomLift (𝟙 W) ψ := by
  have h := (IsHomLift.lift_eqToHom_comp_iff (p := p) _ ψ hx).mp hψ
  exact (IsHomLift.lift_comp_eqToHom_iff (p := p) (𝟙 W) ψ hy.symm).mp (by rwa [Category.id_comp])

section Algebra

variable {A' : Type u} [CommRing A'] {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ)
  (C' : Type u) [CommRing C'] [Algebra A' C'] (hC : Cardinal.mk C' < κ)

/-- **The triple overlap is a pushout**: `C' ⊗ C' ⊗ C'` is the pushout of the last vertex and
the vertex `0` of `C' ⊗ C'`, along the faces `d₂` and `d₀`. -/
theorem isPushout_nerve_two :
    IsPushout (CommRingCat.ofHom ((SmallAlg.homMk (R := nerve (A' := A') hκ C' hC 0)
        (R' := nerve (A' := A') hκ C' hC 1) (vₗ A' C' 1)).hom.hom :
          (nerve (A' := A') hκ C' hC 0).obj →+* (nerve (A' := A') hκ C' hC 1).obj))
      (CommRingCat.ofHom ((SmallAlg.homMk (R := nerve (A' := A') hκ C' hC 0)
        (R' := nerve (A' := A') hκ C' hC 1) (v₀ A' C' 1)).hom.hom :
          (nerve (A' := A') hκ C' hC 0).obj →+* (nerve (A' := A') hκ C' hC 1).obj))
      (CommRingCat.ofHom ((SmallAlg.homMk (R := nerve (A' := A') hκ C' hC 1)
        (R' := nerve (A' := A') hκ C' hC 2) (face A' C' 1 2)).hom.hom :
          (nerve (A' := A') hκ C' hC 1).obj →+* (nerve (A' := A') hκ C' hC 2).obj))
      (CommRingCat.ofHom ((SmallAlg.homMk (R := nerve (A' := A') hκ C' hC 1)
        (R' := nerve (A' := A') hκ C' hC 2) (face A' C' 1 0)).hom.hom :
          (nerve (A' := A') hκ C' hC 1).obj →+* (nerve (A' := A') hκ C' hC 2).obj)) := by
  have t := CommRingCat.isPushout_tensorProduct A' C' C'
  have s := CommRingCat.isPushout_tensorProduct A' (C' ⊗[A'] C') C'
  refine (IsPushout.of_left (h₁₁ := CommRingCat.ofHom (algebraMap A' C'))
    (v₁₁ := CommRingCat.ofHom (algebraMap A' C'))
    (v₁₂ := CommRingCat.ofHom ((vₗ A' C' 1 : C' →ₐ[A'] C' ⊗[A'] C') : C' →+* C' ⊗[A'] C'))
    (h₂₁ := CommRingCat.ofHom ((v₀ A' C' 1 : C' →ₐ[A'] C' ⊗[A'] C') : C' →+* C' ⊗[A'] C'))
    (isPushout_congr s ?_ rfl rfl ?_) ?_ (isPushout_congr t rfl rfl rfl rfl)).flip
  · ext a
    exact (AlgHom.commutes (v₀ A' C' 1) a).symm
  · ext c
    show ((1 : C' ⊗[A'] C') ⊗ₜ[A'] c : (C' ⊗[A'] C') ⊗[A'] C') =
      face A' C' 1 2 ((1 : C') ⊗ₜ[A'] c)
    rw [show (2 : Fin 3) = Fin.succ 1 from rfl, face_succ_tmul]
    rfl
  · ext c
    rfl

end Algebra

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {U₀ : BigFppfOver B S hS} (a : schemeFibredCategory B S hS U₀ ⟶ 𝒳)
  {P : SmallAlg (ringOf B S hS T') B.cutoff} (ι : specOver P ⟶ U₀)

namespace StackChart

/-- The restriction of `ξ w` along `Spec h`: the object `ξ (h ∘ w)` with the cartesian arrow
`trans h w`. -/
noncomputable abbrev resPt {C D : SmallAlg (ringOf B S hS T') B.cutoff} (h : C ⟶ D)
    (w : P.obj →ₐ[ringOf B S hS T'] C.obj) :
    Functor.Restriction 𝒳.val.p (specOverMap h) (ξ a ι w) (ξ_obj a ι w) where
  pt := ξ a ι (h.hom.hom.comp w)
  hpt := ξ_obj a ι _
  hom := trans a ι h w
  isHomLift := inferInstance
  isCart := 𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift _ _

/-- The comparison between two restrictions `resPt` is the arrow `trans`. -/
theorem compTo_resPt {C D E : SmallAlg (ringOf B S hS T') B.cutoff} (h : C ⟶ D) (g : D ⟶ E)
    (k : C ⟶ E) (hk : h ≫ g = k) (hh : specOverMap k = specOverMap g ≫ specOverMap h)
    (w : P.obj →ₐ[ringOf B S hS T'] C.obj) :
    Functor.Restriction.compTo 𝒳.val.p (specOverMap g) (specOverMap h) hh (resPt a ι h w)
        (resPt a ι k w) =
      eqToHom (congrArg (fun m : C ⟶ E ↦ ξ a ι (m.hom.hom.comp w)) hk.symm) ≫
        trans a ι g (h.hom.hom.comp w) := by
  subst hk
  exact (Functor.Restriction.compTo_eq' 𝒳.val.p _ _ hh _ _ _ (trans_isHomLift a ι g _)
    (trans_comp a ι h g w).symm).trans
    (Category.id_comp _).symm

/-- The comparison into the trivial restriction is the given cartesian arrow. -/
theorem compTo_id {V U : BigFppfOver B S hS} (g : V ⟶ U) {x : 𝒳.val.obj}
    (hx : 𝒳.val.p.obj x = U) (hh : g = g ≫ 𝟙 U) (xr : Functor.Restriction 𝒳.val.p g x hx) :
    Functor.Restriction.compTo 𝒳.val.p g (𝟙 U) hh (Functor.Restriction.id 𝒳.val.p x hx) xr =
      xr.hom :=
  (Category.comp_id _).symm.trans
    (Functor.Restriction.compTo_hom 𝒳.val.p g (𝟙 U) hh (Functor.Restriction.id 𝒳.val.p x hx) xr)

variable {a ι}

/-- Equal arrows have equal underlying morphisms, up to the induced identifications of their
source and target. -/
theorem Arr.hom_eq_of_eq {C : SmallAlg (ringOf B S hS T') B.cutoff} {g g' : Arr a ι C}
    (h : g = g') :
    g.hom = eqToHom (by rw [h]) ≫ g'.hom ≫ eqToHom (by rw [h]) := by
  subst h
  simp

/-- A morphism over the identity of `W` is a morphism in the fibre over `W`. -/
theorem fibreHom_of_isHomLift {W : BigFppfOver B S hS} {x y : 𝒳.val.obj}
    (hx : 𝒳.val.p.obj x = W) (hy : 𝒳.val.p.obj y = W) (φ : x ⟶ y)
    [𝒳.val.p.IsHomLift (𝟙 W) φ] : Functor.FibreHom 𝒳.val.p x y hx hy φ := by
  show 𝒳.val.p.IsHomLift (eqToHom hx ≫ eqToHom hy.symm) φ
  rw [← Category.id_comp (eqToHom hy.symm)]
  infer_instance

/-- Precomposing a morphism over `f` with `eqToHom` gives a morphism over `f`. -/
theorem isHomLift_eqToHom_comp {W W' : BigFppfOver B S hS} {f : W ⟶ W'} {x x' y : 𝒳.val.obj}
    (h : x' = x) {φ : x ⟶ y} (hl : 𝒳.val.p.IsHomLift f φ) :
    𝒳.val.p.IsHomLift f (eqToHom h ≫ φ) := by
  have := hl
  infer_instance

/-- For equal morphisms `k = k'`, the arrows `trans k w` and `trans k' w` agree up to
`eqToHom`. -/
theorem trans_eq_of_eq {C D : SmallAlg (ringOf B S hS T') B.cutoff} {k k' : C ⟶ D} (hk : k = k')
    (w : P.obj →ₐ[ringOf B S hS T'] C.obj) :
    trans a ι k w = eqToHom (by rw [hk]) ≫ trans a ι k' w := by
  subst hk
  simp

/-- If `h ≫ g = h' ≫ g'`, then the composite `trans g ∘ trans h` equals `trans (h' ≫ g')`, up
to `eqToHom`. -/
theorem trans_comp_eq_of_eq {C D D' E : SmallAlg (ringOf B S hS T') B.cutoff} (h : C ⟶ D)
    (g : D ⟶ E) (h' : C ⟶ D') (g' : D' ⟶ E) (e : h ≫ g = h' ≫ g')
    (w : P.obj →ₐ[ringOf B S hS T'] C.obj)
    (hX : ξ a ι ((h' ≫ g').hom.hom.comp w) = ξ a ι (g.hom.hom.comp (h.hom.hom.comp w))) :
    (eqToHom hX ≫ trans a ι g (h.hom.hom.comp w)) ≫ trans a ι h w = trans a ι (h' ≫ g') w := by
  calc (eqToHom hX ≫ trans a ι g (h.hom.hom.comp w)) ≫ trans a ι h w
      = eqToHom hX ≫ trans a ι (h ≫ g) w :=
        (Category.assoc _ _ _).trans (congrArg _ (trans_comp a ι h g w).symm)
    _ = eqToHom hX ≫ eqToHom _ ≫ trans a ι (h' ≫ g') w :=
        congrArg _ (trans_eq_of_eq (a := a) (ι := ι) e w)
    _ = trans a ι (h' ≫ g') w := (eqToHom_trans_assoc _ _ _).trans (Category.id_comp _)

section Descent

variable (T') {C' : Type u} [CommRing C'] [Algebra (ringOf B S hS T') C']
  (hC : Cardinal.mk C' < B.cutoff)

/-- The Čech nerve of `A' → C'` as small algebras. -/
abbrev descNerve (n : ℕ) : SmallAlg (ringOf B S hS T') B.cutoff :=
  nerve (A' := ringOf B S hS T') B.aleph0_lt_cutoff C' hC n

/-- The vertex `0` of the double overlap. -/
abbrev descV₀ : descNerve T' hC 0 ⟶ descNerve T' hC 1 :=
  SmallAlg.homMk (v₀ (ringOf B S hS T') C' 1)

/-- The last vertex of the double overlap. -/
abbrev descVₗ : descNerve T' hC 0 ⟶ descNerve T' hC 1 :=
  SmallAlg.homMk (vₗ (ringOf B S hS T') C' 1)

/-- The faces from the double to the triple overlap. -/
abbrev descFace (i : Fin 3) : descNerve T' hC 1 ⟶ descNerve T' hC 2 :=
  SmallAlg.homMk (face (ringOf B S hS T') C' 1 i)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- The simplicial identity `d₀ ∘ v₀ = d₂ ∘ vₗ` from `C'` to the triple overlap. -/
theorem descV₀_face_zero : descV₀ T' hC ≫ descFace T' hC 0 = descVₗ T' hC ≫ descFace T' hC 2 :=
  ObjectProperty.hom_ext _ (CommAlgCat.hom_ext (AlgHom.ext fun _ ↦ rfl))

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- The simplicial identity `d₁ ∘ v₀ = d₂ ∘ v₀` from `C'` to the triple overlap. -/
theorem descV₀_face_one : descV₀ T' hC ≫ descFace T' hC 1 = descV₀ T' hC ≫ descFace T' hC 2 :=
  ObjectProperty.hom_ext _ (CommAlgCat.hom_ext (AlgHom.ext fun _ ↦ rfl))

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- The simplicial identity `d₁ ∘ vₗ = d₀ ∘ vₗ` from `C'` to the triple overlap. -/
theorem descVₗ_face_one : descVₗ T' hC ≫ descFace T' hC 1 = descVₗ T' hC ≫ descFace T' hC 0 :=
  ObjectProperty.hom_ext _ (CommAlgCat.hom_ext (AlgHom.ext fun _ ↦ rfl))

variable {T'} (hA : Cardinal.mk (ringOf B S hS T') < B.cutoff)

/-- For `C'` faithfully flat and finitely presented over `A'`, the sieve generated by
`Spec C' ⟶ Spec A'` is an fppf covering sieve. -/
theorem ofArrows_baseMap_mem [Module.FaithfullyFlat (ringOf B S hS T') C']
    [Algebra.FinitePresentation (ringOf B S hS T') C'] :
    Sieve.ofArrows (fun _ : PUnit.{w + 1} ↦ specOver (descNerve T' hC 0))
      (fun _ ↦ specOverMap (baseMap B.aleph0_lt_cutoff hC hA)) ∈
        BigFppfOver.topology B S hS (specOver (baseAlg (κ := B.cutoff) hA)) := by
  rw [Sieve.ofArrows, Presieve.ofArrows_pUnit]
  have hFF := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap (ringOf B S hS T') C'))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  have hfp : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap (ringOf B S hS T') C'))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  exact Space.sieve_generate_singleton_mem_topology_over_of_flat B S hS _ hFF.2 hFF.1 hfp

/-- `Spec (C' ⊗ C')` is the fibre product of two copies of `Spec C'` over `Spec A'`. -/
theorem isPullback_descV :
    IsPullback (specOverMap (descV₀ T' hC)) (specOverMap (descVₗ T' hC))
      (specOverMap (baseMap B.aleph0_lt_cutoff hC hA))
      (specOverMap (baseMap B.aleph0_lt_cutoff hC hA)) :=
  isPullback_specOverMap_of_isPushout _ _ _ _ (isPushout_nerve_one B.aleph0_lt_cutoff C' hC hA)

/-- `Spec (C' ⊗ C' ⊗ C')` is the fibre product of two copies of `Spec (C' ⊗ C')` over
`Spec C'`, along the faces `d₂` and `d₀`. -/
theorem isPullback_descFace :
    IsPullback (specOverMap (descFace T' hC 2)) (specOverMap (descFace T' hC 0))
      (specOverMap (descVₗ T' hC)) (specOverMap (descV₀ T' hC)) :=
  isPullback_specOverMap_of_isPushout (descVₗ T' hC) (descV₀ T' hC) (descFace T' hC 2)
    (descFace T' hC 0) (isPushout_nerve_two B.aleph0_lt_cutoff C' hC)

variable {hC} (u : P.obj →ₐ[ringOf B S hS T'] (descNerve T' hC 0).obj)
  (hom : ξ a ι ((descV₀ T' hC).hom.hom.comp u) ⟶ ξ a ι ((descVₗ T' hC).hom.hom.comp u))
  [lift : 𝒳.val.p.IsHomLift (𝟙 (specOver (descNerve T' hC 1))) hom]

/-- The arrow over the double overlap. -/
abbrev descArr : Arr a ι (descNerve T' hC 1) := ⟨_, _, hom, lift⟩

/-- The source of the pullback of `r` along `d₀` is the target of its pullback along `d₂`. -/
theorem desc_mid : (Arr.map a ι (descFace T' hC 0) (descArr u hom)).src =
    (Arr.map a ι (descFace T' hC 2) (descArr u hom)).tgt :=
  congrArg (fun m : descNerve T' hC 0 ⟶ descNerve T' hC 2 ↦ m.hom.hom.comp u)
    (descV₀_face_zero T' hC)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- The points `(d₂ ∘ v₀) ∘ u` and `d₁ ∘ (v₀ ∘ u)` of the triple overlap agree. -/
theorem desc_e₁ : ((descV₀ T' hC ≫ descFace T' hC 2).hom.hom.comp u) =
    (descFace T' hC 1).hom.hom.comp ((descV₀ T' hC).hom.hom.comp u) :=
  congrArg (fun m : descNerve T' hC 0 ⟶ descNerve T' hC 2 ↦ m.hom.hom.comp u)
    (descV₀_face_one T' hC).symm

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- The points `d₁ ∘ (vₗ ∘ u)` and `(d₀ ∘ vₗ) ∘ u` of the triple overlap agree. -/
theorem desc_e₂ : (descFace T' hC 1).hom.hom.comp ((descVₗ T' hC).hom.hom.comp u) =
    ((descVₗ T' hC ≫ descFace T' hC 0).hom.hom.comp u) :=
  congrArg (fun m : descNerve T' hC 0 ⟶ descNerve T' hC 2 ↦ m.hom.hom.comp u)
    (descVₗ_face_one T' hC)

/-- The pullback of `r` along the face `d₂` is a restriction of `r`. -/
theorem desc_restr₀₁ : Functor.IsRestrictionOf 𝒳.val.p (specOverMap (descFace T' hC 2))
    (specOverMap_comp _ _) (specOverMap_comp _ _) (resPt a ι (descV₀ T' hC) u)
    (resPt a ι (descVₗ T' hC) u) (resPt a ι (descV₀ T' hC ≫ descFace T' hC 2) u)
    (resPt a ι (descVₗ T' hC ≫ descFace T' hC 2) u) hom
    (Arr.map a ι (descFace T' hC 2) (descArr u hom)).hom :=
  Functor.isRestrictionOf_of_fac _ _ _ _ _ _ _ _ _ _
    (trans a ι (descFace T' hC 2) ((descV₀ T' hC).hom.hom.comp u))
    (trans_isHomLift a ι (descFace T' hC 2) ((descV₀ T' hC).hom.hom.comp u))
    (trans_comp a ι (descV₀ T' hC) (descFace T' hC 2) u).symm
    (trans a ι (descFace T' hC 2) ((descVₗ T' hC).hom.hom.comp u))
    (trans_isHomLift a ι (descFace T' hC 2) ((descVₗ T' hC).hom.hom.comp u))
    (trans_comp a ι (descVₗ T' hC) (descFace T' hC 2) u).symm
    (Arr.map_hom_fac (descFace T' hC 2) (descArr u hom))

/-- The pullback of `r` along the face `d₀` is a restriction of `r`. -/
theorem desc_restr₁₂ : Functor.IsRestrictionOf 𝒳.val.p (specOverMap (descFace T' hC 0))
    ((specOverMap_comp _ _).trans (isPullback_descFace hC).w) (specOverMap_comp _ _)
    (resPt a ι (descV₀ T' hC) u)
    (resPt a ι (descVₗ T' hC) u) (resPt a ι (descVₗ T' hC ≫ descFace T' hC 2) u)
    (resPt a ι (descVₗ T' hC ≫ descFace T' hC 0) u) hom
    (eqToHom (congrArg (ξ a ι) (desc_mid u hom).symm) ≫
      (Arr.map a ι (descFace T' hC 0) (descArr u hom)).hom) :=
  Functor.isRestrictionOf_of_fac _ _ _ _ _ _ _ _ _ _
    (eqToHom (congrArg (ξ a ι) (desc_mid u hom).symm) ≫
      trans a ι (descFace T' hC 0) ((descV₀ T' hC).hom.hom.comp u))
    (isHomLift_eqToHom_comp _ (trans_isHomLift a ι (descFace T' hC 0) _))
    (trans_comp_eq_of_eq _ _ _ _ (descV₀_face_zero T' hC) u _)
    (trans a ι (descFace T' hC 0) ((descVₗ T' hC).hom.hom.comp u))
    (trans_isHomLift a ι (descFace T' hC 0) ((descVₗ T' hC).hom.hom.comp u))
    (trans_comp a ι (descVₗ T' hC) (descFace T' hC 0) u).symm
    ((Category.assoc _ _ _).trans ((congrArg (eqToHom _ ≫ ·)
      (Arr.map_hom_fac (descFace T' hC 0) (descArr u hom))).trans (Category.assoc _ _ _).symm))

/-- The pullback of `r` along the face `d₁` is a restriction of `r`. -/
theorem desc_restr₀₂ : Functor.IsRestrictionOf 𝒳.val.p (specOverMap (descFace T' hC 1))
    ((congrArg specOverMap (descV₀_face_one T' hC).symm).trans (specOverMap_comp _ _))
    ((congrArg specOverMap (descVₗ_face_one T' hC).symm).trans (specOverMap_comp _ _))
    (resPt a ι (descV₀ T' hC) u)
    (resPt a ι (descVₗ T' hC) u) (resPt a ι (descV₀ T' hC ≫ descFace T' hC 2) u)
    (resPt a ι (descVₗ T' hC ≫ descFace T' hC 0) u) hom
    (eqToHom (congrArg (ξ a ι) (desc_e₁ u)) ≫ (Arr.map a ι (descFace T' hC 1) (descArr u hom)).hom ≫
        eqToHom (congrArg (ξ a ι) (desc_e₂ u))) := by
  refine Functor.isRestrictionOf_of_fac _ _ _ _ _ _ _ _ _ _
    (eqToHom (congrArg (ξ a ι) (desc_e₁ u)) ≫
      trans a ι (descFace T' hC 1) ((descV₀ T' hC).hom.hom.comp u))
    (isHomLift_eqToHom_comp _ (trans_isHomLift a ι (descFace T' hC 1) _))
    (trans_comp_eq_of_eq _ _ _ _ (descV₀_face_one T' hC) u _)
    (eqToHom (congrArg (ξ a ι) (desc_e₂ u).symm) ≫
      trans a ι (descFace T' hC 1) ((descVₗ T' hC).hom.hom.comp u))
    (isHomLift_eqToHom_comp _ (trans_isHomLift a ι (descFace T' hC 1) _))
    (trans_comp_eq_of_eq _ _ _ _ (descVₗ_face_one T' hC) u _) ?_
  calc _ = eqToHom (congrArg (ξ a ι) (desc_e₁ u)) ≫
        ((Arr.map a ι (descFace T' hC 1) (descArr u hom)).hom ≫
          trans a ι (descFace T' hC 1) ((descVₗ T' hC).hom.hom.comp u)) :=
      (Category.assoc _ _ _).trans (congrArg _ ((Category.assoc _ _ _).trans
        (congrArg _ ((eqToHom_trans_assoc _ _ _).trans (Category.id_comp _)))))
    _ = eqToHom (congrArg (ξ a ι) (desc_e₁ u)) ≫
        (trans a ι (descFace T' hC 1) ((descV₀ T' hC).hom.hom.comp u) ≫ hom) :=
      congrArg _ (Arr.map_hom_fac (descFace T' hC 1) (descArr u hom))
    _ = _ := (Category.assoc _ _ _).symm

/-- The descent datum of `(ξ u, r)` along `Spec C' ⟶ Spec A'`. -/
noncomputable def descDatum
    (hcoc : Arr.comp (Arr.map a ι (descFace T' hC 0) (descArr u hom))
      (Arr.map a ι (descFace T' hC 2) (descArr u hom)) (desc_mid u hom) =
      Arr.map a ι (descFace T' hC 1) (descArr u hom)) :
    Functor.DescentDatum 𝒳.val.p (fun _ : PUnit.{w + 1} ↦ specOver (descNerve T' hC 0))
      (fun _ ↦ specOverMap (baseMap B.aleph0_lt_cutoff hC hA))
      (fun _ _ ↦ specOver (descNerve T' hC 1)) (fun _ _ ↦ specOverMap (descV₀ T' hC))
      (fun _ _ ↦ specOverMap (descVₗ T' hC)) (fun _ _ ↦ isPullback_descV hC hA)
      (fun _ _ _ ↦ specOver (descNerve T' hC 2)) (fun _ _ _ ↦ specOverMap (descFace T' hC 2))
      (fun _ _ _ ↦ specOverMap (descFace T' hC 0)) (fun _ _ _ ↦ isPullback_descFace hC)
      (fun _ _ _ ↦ specOverMap (descV₀ T' hC ≫ descFace T' hC 2))
      (fun _ _ _ ↦ specOverMap (descVₗ T' hC ≫ descFace T' hC 2))
      (fun _ _ _ ↦ specOverMap (descVₗ T' hC ≫ descFace T' hC 0))
      (fun _ _ _ ↦ specOverMap_comp _ _) (fun _ _ _ ↦ specOverMap_comp _ _)
      (fun _ _ _ ↦ specOverMap_comp _ _) where
  x _ := ξ a ι u
  hx _ := ξ_obj a ι u
  xrij _ _ := resPt a ι (descV₀ T' hC) u
  xrji _ _ := resPt a ι (descVₗ T' hC) u
  φ _ _ := hom
  φ_fibreHom _ _ := fibreHom_of_isHomLift _ _ hom
  φ_iso _ _ := Arr.isIso_hom (descArr u hom)
  wi _ _ _ := resPt a ι (descV₀ T' hC ≫ descFace T' hC 2) u
  wj _ _ _ := resPt a ι (descVₗ T' hC ≫ descFace T' hC 2) u
  wk _ _ _ := resPt a ι (descVₗ T' hC ≫ descFace T' hC 0) u
  αij _ _ _ := (Arr.map a ι (descFace T' hC 2) (descArr u hom)).hom
  αjk _ _ _ := eqToHom (congrArg (ξ a ι) (desc_mid u hom).symm) ≫
    (Arr.map a ι (descFace T' hC 0) (descArr u hom)).hom
  αik _ _ _ := eqToHom (congrArg (ξ a ι) (desc_e₁ u)) ≫
    (Arr.map a ι (descFace T' hC 1) (descArr u hom)).hom ≫ eqToHom (congrArg (ξ a ι) (desc_e₂ u))
  αij_restr _ _ _ := desc_restr₀₁ u hom
  αjk_restr _ _ _ := desc_restr₁₂ u hom
  s₁₃ _ _ _ := specOverMap (descFace T' hC 1)
  hs₁₃₁ _ _ _ := (specOverMap_comp _ _).symm.trans (congrArg specOverMap (descV₀_face_one T' hC))
  hs₁₃₂ _ _ _ :=
    (specOverMap_comp _ _).symm.trans (congrArg specOverMap (descVₗ_face_one T' hC).symm)
  αik_restr _ _ _ := desc_restr₀₂ u hom
  cocycle _ _ _ := (Arr.hom_eq_of_eq hcoc).symm

/-- Given a restriction `xr` of `x` along `Spec C' ⟶ Spec A'` and a fibre isomorphism
`ψ : xr.pt ⟶ ξ u`, the morphism `ψ⁻¹ ≫ xr.hom` lies over `Spec C' ⟶ Spec A'`. -/
theorem isHomLift_desc {x : 𝒳.val.obj} (hx : 𝒳.val.p.obj x = specOver (baseAlg (κ := B.cutoff) hA))
    (xr : Functor.Restriction 𝒳.val.p (specOverMap (baseMap B.aleph0_lt_cutoff hC hA)) x hx)
    (ψ : xr.pt ⟶ ξ a ι u) (hψi : IsIso ψ)
    (hψ : Functor.FibreHom 𝒳.val.p xr.pt (ξ a ι u) xr.hpt (ξ_obj a ι u) ψ) :
    𝒳.val.p.IsHomLift (specOverMap (baseMap B.aleph0_lt_cutoff hC hA)) (inv ψ ≫ xr.hom) := by
  have := hψi
  have := Functor.isHomLift_id_of_fibreHom _ hψ
  have := Functor.isHomLift_of_restriction _ xr
  infer_instance

/-- **Effective descent of a point of a chart along a faithfully flat finitely presented
algebra.** A point `u : P → C'` and an arrow `r` of `𝒳` over `Spec (C' ⊗ C')` from `ξ (v₀ ∘ u)`
to `ξ (vₗ ∘ u)` satisfying the cocycle condition over `Spec (C' ⊗ C' ⊗ C')` descend: there is an
object `x'` over `Spec A'` and a morphism `ζ : ξ u ⟶ x'` over `Spec C' ⟶ Spec A'` whose two
pullbacks to `Spec (C' ⊗ C')` differ by `r`. -/
theorem exists_descent_of_hom (h𝒳 : 𝒳.val.p.IsStackInGroupoids.{w} (BigFppfOver.topology B S hS))
    [Module.FaithfullyFlat (ringOf B S hS T') C'] [Algebra.FinitePresentation (ringOf B S hS T') C']
    (hcoc : Arr.comp (Arr.map a ι (descFace T' hC 0) (descArr u hom))
      (Arr.map a ι (descFace T' hC 2) (descArr u hom)) (desc_mid u hom) =
      Arr.map a ι (descFace T' hC 1) (descArr u hom)) :
    ∃ (x' : 𝒳.val.obj) (ζ : ξ a ι u ⟶ x'),
      𝒳.val.p.IsHomLift (specOverMap (baseMap B.aleph0_lt_cutoff hC hA)) ζ ∧
        hom ≫ trans a ι (descVₗ T' hC) u ≫ ζ = trans a ι (descV₀ T' hC) u ≫ ζ := by
  obtain ⟨x, hx, xr, ψ, hψf, hψi, hcomp⟩ := h𝒳.effective_descent _ _
    (ofArrows_baseMap_mem hC hA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ (descDatum hA u hom hcoc)
  let i₀ : PUnit.{w + 1} := PUnit.unit
  obtain ⟨xrij, ψir, ψjr, -, -, hir, -, hr₁, hr₂, hc⟩ := hcomp i₀ i₀
  have := hψi i₀
  have := hir
  let ζ := inv (ψ i₀) ≫ (xr i₀).hom
  refine ⟨x, ζ, isHomLift_desc hA u hx (xr i₀) (ψ i₀) (hψi i₀) (hψf i₀), ?_⟩
  have hζ : ψ i₀ ≫ ζ = (xr i₀).hom := IsIso.hom_inv_id_assoc _ _
  have key : ∀ {y : 𝒳.val.obj} (c : xrij.pt ⟶ (xr i₀).pt) (n : xrij.pt ⟶ y) (m : y ⟶ ξ a ι u),
      c ≫ (xr i₀).hom = xrij.hom → n ≫ m = c ≫ ψ i₀ → n ≫ m ≫ ζ = xrij.hom := fun c n m hc hn ↦
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ζ) hn).trans
      ((Category.assoc _ _ _).trans ((congrArg (c ≫ ·) hζ).trans hc)))
  have E₁ := key _ _ _ (Functor.Restriction.compTo_hom _ _ _ rfl _ _) (by
    unfold Functor.IsRestrictionOf at hr₁
    rwa [compTo_id] at hr₁)
  have E₂ := key _ _ _ (Functor.Restriction.compTo_hom _ _ _ (isPullback_descV hC hA).w _ _) (by
    unfold Functor.IsRestrictionOf at hr₂
    rwa [compTo_id] at hr₂)
  have hc' : ψir ≫ hom = ψjr := hc
  refine (cancel_epi ψir).mp ?_
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hc').trans (E₂.trans E₁.symm))

end Descent

end StackChart

end AlgebraicGeometry.Stack.GroupoidLift

end
