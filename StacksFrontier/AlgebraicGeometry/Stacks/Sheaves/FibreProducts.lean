module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.FibreProducts
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory

/-!
# Fibre products in categories fibred in groupoids over a big fppf site

A category fibred in groupoids over the big fppf category of a scheme has fibre products, and
a morphism of such categories carries fibre product squares to fibre product squares. If the
morphism is moreover faithful, it carries equalizer diagrams to equalizer diagrams.

Fibre products are produced by combining the fibre products of the base slice category with
the statement that a category fibred in groupoids has whatever fibre products its base has
(Stacks 06N6). Preservation of fibre products is the reflection half of the same statement
applied to the target. Preservation of equalizers needs more: a monomorphism of the source is
shown to have monic image in the base, which makes the image of an equalizer fork into a fork
with monic leg, and the fill-in axiom of the target then produces the mediating morphism and
its uniqueness.

## Main results

* `AlgebraicGeometry.BigFppfOver.hasPullbacks_of_isFiberedInGroupoids`: a category fibred in
  groupoids over the big fppf category of a scheme has fibre products.
* `CategoryTheory.CatFiberedInGroupoids.preservesPullbacks_homFunctor`: a morphism of
  categories fibred in groupoids over a base with fibre products preserves fibre products.
* `CategoryTheory.CatFiberedInGroupoids.mono_map_of_mono`: the base image of a monomorphism of
  a category fibred in groupoids is a monomorphism.
* `CategoryTheory.CatFiberedInGroupoids.map_eq_of_comp_eq`: the base morphisms of a functor
  over two projections, compared through the equality of the composites.
* `CategoryTheory.CatFiberedInGroupoids.isLimitForkMap`: a faithful functor between categories
  fibred in groupoids over a common base carries an equalizer fork to an equalizer fork.
* `CategoryTheory.CatFiberedInGroupoids.preservesEqualizers_homFunctor_of_faithful`: a
  faithful morphism of categories fibred in groupoids preserves equalizers.

## Implementation notes

Only `hasPullbacks_of_isFiberedInGroupoids` mentions the fppf site; it is the statement whose
base category is the one the source works over. The two preservation statements use nothing
about the fppf topology beyond the existence of fibre products in the base, so they are stated
over an arbitrary base category and apply in particular to `AlgebraicGeometry.BigFppfOver`.

## References

* [Stacks Project, Tag 06WY](https://stacks.math.columbia.edu/tag/06WY)
* [Stacks Project, Tag 06WZ](https://stacks.math.columbia.edu/tag/06WZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.BigFppfOver

universe u

/-- **Stacks 06WY, part (1).** A category fibred in groupoids over the big fppf category of a
scheme has fibre products. -/
@[stacks 06WY "part (1)"]
theorem hasPullbacks_of_isFiberedInGroupoids
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : Type*} [Category 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) :
    HasPullbacks 𝒳 :=
  @hasPullbacks_of_hasLimit_cospan _ _ fun {_ _ _} {f g} => hp.hasPullback p f g

end AlgebraicGeometry.BigFppfOver

namespace CategoryTheory.CatFiberedInGroupoids

universe v₁ v₂ u₁ u₂

section Pullbacks

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] [HasPullbacks 𝒞]
variable {𝒳 𝒴 : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞}

/-- **Stacks 06WZ.** A morphism of categories fibred in groupoids over a base category with
fibre products preserves fibre products. -/
@[stacks 06WZ "preserves_fibre_products"]
instance preservesPullbacks_homFunctor (f : 𝒳 ⟶ 𝒴) :
    PreservesLimitsOfShape WalkingCospan (homFunctor f) where
  preservesLimit {K} := by
    set F := homFunctor f
    have key : ∀ {X Y Z : 𝒳.val.obj} (g : X ⟶ Z) (h : Y ⟶ Z),
        PreservesLimit (cospan g h) F := by
      intro X Y Z g h
      have : HasPullback g h := 𝒳.isFiberedInGroupoids.hasPullback 𝒳.val.p g h
      have hX : IsPullback (pullback.fst g h) (pullback.snd g h) g h :=
        IsPullback.of_hasPullback g h
      have hBase := 𝒳.isFiberedInGroupoids.map_isPullback 𝒳.val.p g h
        (pullback.fst g h) (pullback.snd g h) hX
      rw [← homFunctor_comp_p f] at hBase
      have hTarget : IsPullback (F.map (pullback.fst g h)) (F.map (pullback.snd g h))
          (F.map g) (F.map h) := by
        apply 𝒴.isFiberedInGroupoids.isPullback_of_map_isPullback
        · rw [← F.map_comp, ← F.map_comp, hX.w]
        · simpa only [Functor.comp_map] using hBase
      exact preservesLimit_of_preserves_limit_cone hX.isLimit
        ((isLimitMapConePullbackConeEquiv F hX.w).symm hTarget.isLimit)
    have := key (K.map WalkingCospan.Hom.inl) (K.map WalkingCospan.Hom.inr)
    exact preservesLimit_of_iso_diagram F (diagramIsoCospan K).symm

end Pullbacks

section Equalizers

variable {A B C : Type*} [Category A] [Category B] [Category C]

/-- A monomorphism of a category fibred in groupoids has monic image in the base: lifting the
two competing base morphisms and using the fill-in axiom identifies them already upstairs. -/
theorem mono_map_of_mono (p : A ⥤ C) (hp : p.IsFiberedInGroupoids) {x y : A} (f : x ⟶ y)
    [Mono f] : Mono (p.map f) := by
  refine ⟨fun {z} a b hab => ?_⟩
  obtain ⟨x₁, m₁, hm₁⟩ := hp.exists_lift a x rfl
  obtain ⟨x₂, m₂, hm₂⟩ := hp.exists_lift b x rfl
  have d₁ := IsHomLift.domain_eq p a m₁
  have d₂ := IsHomLift.domain_eq p b m₂
  let e : p.obj x₁ ⟶ p.obj x₂ := eqToHom (d₁.trans d₂.symm)
  have hm₁' : p.map m₁ = eqToHom d₁ ≫ a := by simpa using IsHomLift.fac' p a m₁
  have hm₂' : p.map m₂ = eqToHom d₂ ≫ b := by simpa using IsHomLift.fac' p b m₂
  have hc : e ≫ p.map (m₂ ≫ f) = p.map (m₁ ≫ f) := by
    simp only [Functor.map_comp]
    rw [hm₂', hm₁']
    simp [e, hab]
  have : p.IsStronglyCartesian (p.map (m₂ ≫ f)) (m₂ ≫ f) := hp.isStronglyCartesian (m₂ ≫ f)
  let χ := Functor.IsStronglyCartesian.map p (p.map (m₂ ≫ f)) (m₂ ≫ f) hc.symm (m₁ ≫ f)
  have hχ : χ ≫ (m₂ ≫ f) = m₁ ≫ f :=
    Functor.IsStronglyCartesian.fac p (p.map (m₂ ≫ f)) (m₂ ≫ f) hc.symm (m₁ ≫ f)
  have hχm : χ ≫ m₂ = m₁ := (cancel_mono f).1 (by simpa using hχ)
  have hbase : p.map χ = e := (IsHomLift.eq_of_isHomLift p e χ).symm
  calc
    a = eqToHom d₁.symm ≫ p.map m₁ := by simp [hm₁']
    _ = eqToHom d₁.symm ≫ (p.map χ ≫ p.map m₂) := by rw [← Functor.map_comp, hχm]
    _ = b := by simp [hbase, e, hm₂']

/-- Transport of the base morphism of a functor along an equality of composites with the
projections to the base. -/
theorem map_eq_of_comp_eq (F : A ⥤ B) (p : A ⥤ C) (q : B ⥤ C) (h : F ⋙ q = p)
    {x y : A} (m : x ⟶ y) :
    q.map (F.map m) =
      eqToHom (congrArg (fun G : A ⥤ C => G.obj x) h) ≫ p.map m ≫
        eqToHom (congrArg (fun G : A ⥤ C => G.obj y) h).symm := by
  cases h
  simp

/-- The image of the fork condition of an equalizer fork under a functor. -/
theorem forkMap_condition (F : A ⥤ B) {X Y : A} {f g : X ⟶ Y} (t : Fork f g) :
    F.map t.ι ≫ F.map f = F.map t.ι ≫ F.map g := by
  rw [← F.map_comp, ← F.map_comp, t.condition]

/-- A faithful functor between two categories fibred in groupoids over a common base carries
an equalizer fork to an equalizer fork. -/
noncomputable def isLimitForkMap (F : A ⥤ B) (p : A ⥤ C) (q : B ⥤ C) (h : F ⋙ q = p)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    [Functor.Faithful F] {X Y : A} {f g : X ⟶ Y} (t : Fork f g) (ht : IsLimit t) :
    IsLimit (Fork.ofι (F.map t.ι) (forkMap_condition F t)) := by
  refine Fork.IsLimit.mk' _ fun s => ?_
  have wx := congrArg (fun G : A ⥤ C => G.obj X) h
  let b : q.obj s.pt ⟶ p.obj X := q.map s.ι ≫ eqToHom wx
  let lift := hp.exists_lift b X rfl
  let x' := Classical.choose lift
  let m := Classical.choose (Classical.choose_spec lift)
  have hm : p.IsHomLift b m := Classical.choose_spec (Classical.choose_spec lift)
  have d := IsHomLift.domain_eq p b m
  have wx' := congrArg (fun G : A ⥤ C => G.obj x') h
  let k : q.obj (F.obj x') ⟶ q.obj s.pt := eqToHom wx' ≫ eqToHom d
  have hm' : p.map m = eqToHom d ≫ b := by simpa using IsHomLift.fac' p b m
  have hFm : q.map (F.map m) = k ≫ q.map s.ι := by
    rw [map_eq_of_comp_eq F p q h m, hm']
    simp [k, b]
  have : q.IsStronglyCartesian (q.map s.ι) s.ι := hq.isStronglyCartesian s.ι
  let η := Functor.IsStronglyCartesian.map q (q.map s.ι) s.ι hFm (F.map m)
  have hη : η ≫ s.ι = F.map m :=
    Functor.IsStronglyCartesian.fac q (q.map s.ι) s.ι hFm (F.map m)
  have : q.IsStronglyCartesian k η := hq.isStronglyCartesian_homLift k η
  have : IsIso η := Functor.IsStronglyCartesian.isIso_of_base_isIso q k η
  have hmEq : m ≫ f = m ≫ g := F.map_injective (by
    rw [F.map_comp, F.map_comp, ← hη, Category.assoc, Category.assoc, s.condition])
  let a := ht.lift (Fork.ofι m hmEq)
  have ha : a ≫ t.ι = m := ht.fac (Fork.ofι m hmEq) WalkingParallelPair.zero
  let out : s.pt ⟶ F.obj t.pt := inv η ≫ F.map a
  have hout : out ≫ F.map t.ι = s.ι := by simp [out, ← Functor.map_comp, ha, hη]
  have : Mono t.ι := Fork.IsLimit.mono ht
  have : Mono (p.map t.ι) := mono_map_of_mono p hp t.ι
  have : Mono (q.map (F.map t.ι)) := by
    rw [map_eq_of_comp_eq F p q h t.ι]
    infer_instance
  refine ⟨out, hout, fun {l} hl => ?_⟩
  have hleft : l ≫ F.map t.ι = s.ι := by simpa using hl
  have hbase : q.map l = q.map out :=
    (cancel_mono (q.map (F.map t.ι))).1 (by rw [← q.map_comp, ← q.map_comp, hleft, hout])
  have : q.IsHomLift (q.map l) out := by
    rw [hbase]
    infer_instance
  have : q.IsStronglyCartesian (q.map (F.map t.ι)) (F.map t.ι) :=
    hq.isStronglyCartesian (F.map t.ι)
  exact Functor.IsStronglyCartesian.ext q (q.map (F.map t.ι)) (F.map t.ι) (q.map l)
    (by rw [hleft, hout])

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
variable {𝒳 𝒴 : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞}

/-- **Stacks 06WZ.** A faithful morphism of categories fibred in groupoids preserves
equalizers. -/
@[stacks 06WZ "preserves_equalizers"]
instance preservesEqualizers_homFunctor_of_faithful (f : 𝒳 ⟶ 𝒴)
    [Functor.Faithful (homFunctor f)] :
    PreservesLimitsOfShape WalkingParallelPair (homFunctor f) where
  preservesLimit {K} := by
    refine ⟨fun {c} hc => ?_⟩
    set F := homFunctor f
    let f₀ : K.obj WalkingParallelPair.zero ⟶ K.obj WalkingParallelPair.one :=
      K.map WalkingParallelPairHom.left
    let g₀ : K.obj WalkingParallelPair.zero ⟶ K.obj WalkingParallelPair.one :=
      K.map WalkingParallelPairHom.right
    let pp := parallelPair f₀ g₀
    let e := diagramIsoParallelPair K
    have : HasLimit K := HasLimit.mk ⟨c, hc⟩
    have : HasLimit pp := hasLimit_of_iso e
    have : PreservesLimit pp F := by
      have hl := equalizerIsEqualizer f₀ g₀
      exact preservesLimit_of_preserves_limit_cone hl
        ((isLimitMapConeForkEquiv F (equalizer.condition f₀ g₀)).symm
          (isLimitForkMap F 𝒳.val.p 𝒴.val.p (homFunctor_comp_p f) 𝒳.isFiberedInGroupoids
            𝒴.isFiberedInGroupoids
            (Fork.ofι (equalizer.ι f₀ g₀) (equalizer.condition f₀ g₀)) hl))
    exact (preservesLimit_of_iso_diagram F e.symm).preserves hc

end Equalizers

end CategoryTheory.CatFiberedInGroupoids

end
