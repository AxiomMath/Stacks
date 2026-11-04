module

public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.Deformation.Cofibered.Over
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.RimSchlessinger.Basic

/-!
# Transporting the Rim–Schlessinger conditions along a comparison functor

A deformation problem is often presented by a category that is equivalent to, but not equal to,
the category one wants to say the conditions for. This file transports the Rim–Schlessinger
condition and the property of being a deformation category along a functor `F : C ⥤ D` that is
full, faithful and surjective on objects: if `p : D ⥤ 𝒞_Λ` satisfies them, so does `F ⋙ p`.

Such an `F` is an equivalence, but surjectivity on objects on the nose — rather than up to
isomorphism — is what makes the transport available without transporting pullback cones across
an equivalence, and it is what the use sites have: `Over.map e.hom` for an isomorphism `e`.

## Main definitions

* `Deformation.Examples.compFiberFunctor`: the comparison functor on fibres.
* `Deformation.Examples.compFiberEquivalence`: it is an equivalence.

## Main results

* `Deformation.Examples.isHomLift_comp_iff`: a morphism lies over `f` for `F ⋙ p` exactly when
  its image lies over `f` for `p`.
* `Deformation.Examples.isFiberedInGroupoids_comp`: fibered in groupoids is inherited.
* `Deformation.Examples.over_map_obj_surjective`: `Over.map e.hom` is surjective on objects.
* `Deformation.Examples.satisfiesRS_comp`: condition (RS) is inherited.
* `Deformation.Examples.isDeformationCategory_comp`: being a deformation category is inherited.
* `Deformation.Examples.isDeformationCategory_objectsOverFunctor_of_baseIso`: localizing a
  category satisfying (RS) at an object lying over a copy of the residue field gives a
  deformation category.
* `Deformation.objectsOverFunctor_fiber_equiv_punit_of_isTerminal` and
  `Deformation.satisfiesRS_objectsOverFunctor_of_isTerminal` are the variants of the
  localization results of Stacks Tag 06JC in which the base of the chosen object is only
  assumed terminal, rather than equal to `residueFieldObject`.

## Implementation notes

The last two results are the transport that applies when a use site has an object whose base is
terminal but is not literally `residueFieldObject`: the fibre of a functor is indexed by equality
of objects, so the forms of Stacks Tag 06JC recorded in
`StacksFrontier/Deformation/RimSchlessinger/Basic.lean` do not apply to such an object directly.
They live in `namespace Deformation` rather than `Deformation.Examples` because they concern an
arbitrary category over `𝒞_Λ` and no particular example of one.

## References

* [Stacks Project, Tag 06J2](https://stacks.math.columbia.edu/tag/06J2)
* [Stacks Project, Tag 06J9](https://stacks.math.columbia.edu/tag/06J9)
* [Stacks Project, Tag 06JC](https://stacks.math.columbia.edu/tag/06JC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Deformation.Examples

universe u w u₁ v₁ u₂ v₂ u₃ v₃

/-- A morphism lies over `f` for a composite `F ⋙ p` exactly when its image under `F` lies
over `f` for `p`. -/
public theorem isHomLift_comp_iff {C : Type u₁} {D : Type u₂} {B : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} B]
    (F : C ⥤ D) (p : D ⥤ B) {R S : B} {X Y : C} (f : R ⟶ S) (g : X ⟶ Y) :
    (F ⋙ p).IsHomLift f g ↔ p.IsHomLift f (F.map g) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases h
    exact IsHomLift.map _ _
  · exact IsHomLift.of_fac (F ⋙ p) f g
      (IsHomLift.domain_eq p f (F.map g)) (IsHomLift.codomain_eq p f (F.map g))
      (IsHomLift.fac p f (F.map g))

/-- Precomposing a functor fibered in groupoids with a full, faithful functor that is
surjective on objects again gives a functor fibered in groupoids. -/
public theorem isFiberedInGroupoids_comp {C : Type u₁} {D : Type u₂} {B : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} B]
    (F : C ⥤ D) [F.Full] [F.Faithful] (hF : Function.Surjective F.obj)
    (p : D ⥤ B) (hp : p.IsFiberedInGroupoids) : (F ⋙ p).IsFiberedInGroupoids := by
  constructor
  · intro V U f x hx
    obtain ⟨y, g, hg⟩ := hp.exists_lift f (F.obj x) hx
    obtain ⟨y, rfl⟩ := hF y
    exact ⟨y, F.preimage g, (isHomLift_comp_iff F p f _).2 (by simpa using hg)⟩
  · intro x y z g h f hcomm
    obtain ⟨i, ⟨hi, hig⟩, hu⟩ := hp.unique_lift (F.map g) (F.map h) f hcomm
    refine ⟨F.preimage i, ⟨by simpa using hi, F.map_injective (by simpa using hig)⟩,
      fun j ⟨hj, hjg⟩ => F.map_injective ?_⟩
    rw [F.map_preimage]
    exact hu _ ⟨hj, by simpa using congrArg F.map hjg⟩

/-- For an isomorphism `e : x ≅ y`, the functor `Over.map e.hom` is surjective on objects. -/
public theorem over_map_obj_surjective {C : Type u₁} [Category.{v₁} C]
    {x y : C} (e : x ≅ y) : Function.Surjective (Over.map e.hom).obj := by
  intro Y
  refine ⟨(Over.map e.inv).obj Y, ?_⟩
  rcases Y with ⟨a, ⟨⟨⟩⟩, f⟩
  show Over.mk ((f ≫ e.inv) ≫ e.hom) = Over.mk f
  simp

/-- The comparison functor from the fibre of `F ⋙ p` over `b` to the fibre of `p` over `b`. -/
public def compFiberFunctor {C : Type u₁} {D : Type u₂} {B : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} B]
    (F : C ⥤ D) (p : D ⥤ B) (b : B) : (F ⋙ p).Fiber b ⥤ p.Fiber b where
  obj X := ⟨F.obj X.1, X.2⟩
  map f := ⟨F.map f.1, (isHomLift_comp_iff F p _ _).1 f.2⟩
  map_id _ := Subtype.ext (F.map_id _)
  map_comp _ _ := Subtype.ext (F.map_comp _ _)

/-- For `F` full, faithful and surjective on objects, the comparison functor on fibres is an
equivalence. -/
public noncomputable def compFiberEquivalence {C : Type u₁} {D : Type u₂} {B : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} B]
    (F : C ⥤ D) [F.Full] [F.Faithful] (hF : Function.Surjective F.obj)
    (p : D ⥤ B) (b : B) : (F ⋙ p).Fiber b ≌ p.Fiber b := by
  let G := compFiberFunctor F p b
  have : G.Faithful := ⟨fun h => Subtype.ext (F.map_injective (congrArg Subtype.val h))⟩
  have : G.Full := ⟨fun {X Y} f => ⟨⟨F.preimage f.1,
    (isHomLift_comp_iff F p _ _).2 (by
      have h : F.map (F.preimage f.1) = f.1 := F.map_preimage f.1
      rw [h]
      exact f.2)⟩,
    Subtype.ext (F.map_preimage _)⟩⟩
  have : G.EssSurj := ⟨fun Y => by
    obtain ⟨X, hX⟩ := hF Y.1
    have hXb : p.obj (F.obj X) = b := hX ▸ Y.2
    exact ⟨⟨X, hXb⟩, ⟨eqToIso (Subtype.ext hX)⟩⟩⟩
  let : G.IsEquivalence := {}
  exact G.asEquivalence

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Condition (RS) is inherited by the composite with a full, faithful functor that is
surjective on objects. -/
public theorem satisfiesRS_comp
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (F : C ⥤ D) [F.Full] [F.Faithful] (hF : Function.Surjective F.obj)
    (p : D ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k)
    (hp : SatisfiesRS p) : SatisfiesRS (F ⋙ p) := by
  refine ⟨isFiberedInGroupoids_comp F.op (fun X => by
    obtain ⟨Y, hY⟩ := hF X.unop
    exact ⟨Opposite.op Y, congrArg Opposite.op hY⟩) p.op hp.1, ?_⟩
  intro x₁ x₂ x f₁ f₂ hs
  obtain ⟨d, hd, hpd⟩ := hp.2 (F.map f₁) (F.map f₂) hs
  obtain ⟨y, hy⟩ := hF d.pt
  let a : y ⟶ x₁ := F.preimage (eqToHom hy ≫ d.fst)
  let b : y ⟶ x₂ := F.preimage (eqToHom hy ≫ d.snd)
  have ha : F.map a = eqToHom hy ≫ d.fst := F.map_preimage _
  have hb : F.map b = eqToHom hy ≫ d.snd := F.map_preimage _
  have he : a ≫ f₁ = b ≫ f₂ := by
    apply F.map_injective
    rw [F.map_comp, F.map_comp, ha, hb, Category.assoc, Category.assoc, d.condition]
  let c := PullbackCone.mk a b he
  have hi : c.map F ≅ d := PullbackCone.ext (eqToIso hy) ha hb
  have hc : IsLimit c := (IsPullback.of_map F he ⟨⟨(c.map F).condition⟩,
    ⟨PullbackCone.mkSelfIsLimit (IsLimit.ofIsoLimit hd.some hi.symm)⟩⟩).isLimit
  refine ⟨c, ⟨hc⟩, ?_⟩
  have hi' : (c.map F).map p ≅ d.map p := PullbackCone.ext (p.mapIso (eqToIso hy))
    ((congrArg p.map ha).trans (p.map_comp _ _))
    ((congrArg p.map hb).trans (p.map_comp _ _))
  exact ⟨IsLimit.ofIsoLimit hpd.some hi'.symm⟩

/-- Being a deformation category is inherited by the composite with a full, faithful functor
that is surjective on objects. -/
public theorem isDeformationCategory_comp
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (F : C ⥤ D) [F.Full] [F.Faithful] (hF : Function.Surjective F.obj)
    (p : D ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k)
    (hp : IsDeformationCategory p) : IsDeformationCategory (F ⋙ p) := by
  have hrs := satisfiesRS_comp F hF p hp.satisfiesRS
  exact ⟨⟨hrs.1, ⟨(compFiberEquivalence F hF p _).trans
    (hp.predeformation.specialFiber.some.trans (Discrete.equivalence Equiv.punitEquivPUnit))⟩⟩,
    hrs⟩

/-- A category over `𝒞_Λ` satisfying condition (RS) becomes a deformation category when
localized at any object whose image is isomorphic to the residue-field object: the object is
pushed forward into the strict fibre over the residue field, the pushforward morphism is an
isomorphism because it lies over one, and the slice categories are then compared by
`isDeformationCategory_comp`. -/
public theorem isDeformationCategory_objectsOverFunctor_of_baseIso
    {F : Type u₁} [Category.{v₁} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k)
    (hp : SatisfiesRS p) (x : F)
    (ε : p.obj x ≅ residueFieldObject.{u, w, w} Λ k) :
    IsDeformationCategory (objectsOverFunctor p x) := by
  obtain ⟨y, f, hf⟩ := hp.1.exists_lift ε.hom.op (Opposite.op x) rfl
  have hy : p.obj y.unop = residueFieldObject.{u, w, w} Λ k :=
    congrArg Opposite.unop (IsHomLift.domain_eq p.op ε.hom.op f)
  have := hp.1.isStronglyCartesian_homLift ε.hom.op f
  have : IsIso f := Functor.IsStronglyCartesian.isIso_of_base_isIso p.op ε.hom.op f
  exact isDeformationCategory_comp (Over.map (asIso f.unop).hom)
    (over_map_obj_surjective (asIso f.unop))
    (objectsOverFunctor p y.unop)
    (isDeformationCategory_objectsOverFunctor p hp ⟨y.unop, hy⟩)

end Deformation.Examples

namespace Deformation

universe u w u₁ u₂ v₁ v₂

/-- A morphism between objects with terminal image, over a category cofibered in groupoids, is an
isomorphism. -/
private theorem isIso_of_isTerminal_obj {F : Type u₁} [Category.{v₁} F] {C : Type u₂}
    [Category.{v₂} C] (p : F ⥤ C) (hp : p.op.IsFiberedInGroupoids) {a b : F}
    (ha : IsTerminal (p.obj a)) (hb : IsTerminal (p.obj b)) (g : a ⟶ b) : IsIso g :=
  have := isIso_of_isTerminal ha hb (p.map g)
  isIso_of_isCofiberedInGroupoids_of_map_isIso hp g

/-- If `p` is cofibered in groupoids and `p.obj x` is terminal, then for every terminal object
`S` the fibre over `S` of `objectsOverFunctor p x` is equivalent to the one-point category. -/
public theorem objectsOverFunctor_fiber_equiv_punit_of_isTerminal
    {F : Type u₁} [Category.{v₁} F] {C : Type u₂} [Category.{v₂} C]
    (p : F ⥤ C) (hp : p.op.IsFiberedInGroupoids) (x : F)
    (ht : IsTerminal (p.obj x)) (S : C) (hs : IsTerminal S) :
    Nonempty ((objectsOverFunctor p x).Fiber S ≌
      Discrete PUnit.{u₁ + 1}) := by
  classical
  let q := objectsOverFunctor p x
  apply (CategoryTheory.equiv_punit_iff_unique (q.Fiber S)).2
  refine ⟨?_, ?_⟩
  · obtain ⟨b, φ, hφ⟩ := exists_pushforward hp (hs.from (p.obj x)) x rfl
    have hb : p.obj b = S := IsHomLift.codomain_eq p (hs.from (p.obj x)) φ
    have : IsIso φ := isIso_of_isTerminal_obj p hp ht (by simpa [hb] using hs) φ
    let y : Over x := Over.mk (inv φ)
    exact ⟨⟨y, by simpa [q, y] using hb⟩⟩
  · intro y z
    have hterm (w : q.Fiber S) : IsTerminal (p.obj (w.1 : Over x).left) := by
      have hw : p.obj (w.1 : Over x).left = S := by simpa [q] using w.property
      simpa [hw] using hs
    let y0 : Over x := y.1
    let z0 : Over x := z.1
    have : IsIso y0.hom := isIso_of_isTerminal_obj p hp (hterm y) ht y0.hom
    have : IsIso z0.hom := isIso_of_isTerminal_obj p hp (hterm z) ht z0.hom
    let α : y0.left ⟶ z0.left := y0.hom ≫ inv z0.hom
    have htriangle : α ≫ z0.hom = y0.hom := by simp [α]
    let m : y0 ⟶ z0 := Over.homMk α htriangle
    have hm : q.IsHomLift (𝟙 S) m :=
      IsHomLift.of_fac' q _ m y.property z.property ((hterm z).hom_ext _ _)
    let mF : y ⟶ z := ⟨m, hm⟩
    refine ⟨{ default := mF, uniq := ?_ }⟩
    intro f
    apply Functor.Fiber.hom_ext
    apply Over.OverMorphism.ext
    show f.1.left = mF.1.left
    exact (cancel_mono z0.hom).mp (by rw [Over.w f.1, Over.w mF.1])

/-- A pullback cone of `f₁.left` and `f₂.left` lifts to a pullback cone of `f₁` and `f₂` in
`Over x`, with apex `c.fst ≫ A.hom`. -/
private def overPullbackCone {F : Type u₁} [Category.{v₁} F] {x : F} {A B C : Over x}
    {f₁ : A ⟶ C} {f₂ : B ⟶ C} (c : PullbackCone f₁.left f₂.left) : PullbackCone f₁ f₂ :=
  PullbackCone.mk (Over.homMk (U := Over.mk (c.fst ≫ A.hom)) c.fst rfl)
    (Over.homMk c.snd (by
      rw [← Over.w f₂, ← Category.assoc, ← c.condition, Category.assoc, Over.w f₁]
      rfl))
    (Over.OverMorphism.ext c.condition)

/-- The lift to `Over x` of a limit pullback cone of `f₁.left` and `f₂.left` is a limit. -/
private def isLimitOverPullbackCone {F : Type u₁} [Category.{v₁} F] {x : F}
    {A B C : Over x} {f₁ : A ⟶ C} {f₂ : B ⟶ C} (c : PullbackCone f₁.left f₂.left)
    (hc : IsLimit c) : IsLimit (overPullbackCone c) := by
  let toF (s : PullbackCone f₁ f₂) : PullbackCone f₁.left f₂.left :=
    PullbackCone.mk s.fst.left s.snd.left
      (by simpa using congrArg (fun g => g.left) s.condition)
  refine PullbackCone.isLimitAux _
    (fun s => Over.homMk (U := s.pt) (V := Over.mk (c.fst ≫ A.hom)) (hc.lift (toF s)) (by
      change hc.lift (toF s) ≫ (c.fst ≫ A.hom) = s.pt.hom
      rw [← Category.assoc, hc.fac (toF s) WalkingCospan.left]
      exact s.fst.w))
    (fun s => Over.OverMorphism.ext (hc.fac (toF s) WalkingCospan.left))
    (fun s => Over.OverMorphism.ext (hc.fac (toF s) WalkingCospan.right)) ?_
  intro s m hm
  apply Over.OverMorphism.ext
  apply PullbackCone.IsLimit.hom_ext hc
  · have h := congrArg (fun g => g.left) (hm WalkingCospan.left)
    change m.left ≫ c.fst = s.fst.left at h
    exact h.trans (hc.fac (toF s) WalkingCospan.left).symm
  · have h := congrArg (fun g => g.left) (hm WalkingCospan.right)
    change m.left ≫ c.snd = s.snd.left at h
    exact h.trans (hc.fac (toF s) WalkingCospan.right).symm

/-- If `p : F ⥤ 𝒞_Λ` satisfies condition (RS) and `p.obj x` is terminal, then
`objectsOverFunctor p x` satisfies condition (RS). -/
public theorem satisfiesRS_objectsOverFunctor_of_isTerminal
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k)
    (hp : SatisfiesRS p) (x : F)
    (ht : IsTerminal (p.obj x)) :
    SatisfiesRS
      (objectsOverFunctor p x) := by
  let q := objectsOverFunctor p x
  refine ⟨isCofiberedInGroupoids_overForget hp.1 x ht, ?_⟩
  intro A B C f₁ f₂ hsurj
  change Function.Surjective (p.map f₂.left).hom at hsurj
  obtain ⟨c, ⟨hc⟩, ⟨hcp⟩⟩ := hp.2 f₁.left f₂.left hsurj
  let d : PullbackCone f₁ f₂ := overPullbackCone c
  refine ⟨d, ⟨isLimitOverPullbackCone c hc⟩, ⟨?_⟩⟩
  have hi : d.map q ≅ c.map p :=
    PullbackCone.ext (Iso.refl _)
      (Category.id_comp _).symm (Category.id_comp _).symm
  exact IsLimit.ofIsoLimit hcp hi

end Deformation
