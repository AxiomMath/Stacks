module

public import StacksFrontier.CategoryTheory.Sites.Descent.PullbackDescentData
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.MorGluing

/-!
# Stacks 02ZF: a stack is a fibred category equivalent to its categories of descent data

Let `(𝒮, J)` be a site and let `p : 𝒳 ⥤ 𝒮` be a fibred category over `𝒮`. Every object `x` of the
fibre `𝒳_U` carries a canonical descent datum relative to a covering `𝒰 = {U i ⟶ U}` of `U`, namely
the chosen pullbacks `(f i)^* x` glued by the canonical comparisons of their iterated chosen
pullbacks, and this construction is a functor `𝒳_U ⥤ DD(𝒰)`. This file proves that `p` is a stack
precisely when that functor is an equivalence for every covering of the site.

Both sides are read through the pullback pseudofunctor `U ↦ 𝒳_U` of Stacks 02XO
(`CategoryTheory.Functor.IsFibered.pullbackPseudofunctor`), for which Mathlib's descent API is
available: the category `DD(𝒰)` is `CategoryTheory.Functor.FamilyDescentDatum` of Stacks 02ZD, the
functor is `CategoryTheory.Pseudofunctor.toDescentData`, and Mathlib's
`CategoryTheory.Pseudofunctor.IsStack` for the pullback pseudofunctor is proved here to agree with
`CategoryTheory.Functor.IsStack` for `p`. The two halves of that agreement are the two halves of
the definition of a stack: condition (2) is the identification of the presheaf `Mor(x, y)` of
Stacks 02ZB with Mathlib's `CategoryTheory.Pseudofunctor.presheafHom`, and condition (3) is the
identification of the sieve-indexed descent data `CategoryTheory.Functor.SieveDescentDatum` with
the descent data relative to the covering family consisting of *all* arrows of a covering sieve.

## Main definitions

* `CategoryTheory.Functor.morPresheafIso`, the identification of the presheaf `Mor(x, y)` of
  Stacks 02ZB with the presheaf of morphisms of the pullback pseudofunctor;
* `CategoryTheory.Functor.SieveDescentDatum.toFamily` and
  `CategoryTheory.Functor.SieveDescentDatum.ofFamily`, the two readings of a descent datum relative
  to a covering sieve.

## Main results

* `CategoryTheory.Functor.isStack_iff_isEquivalence_toDescentData`, Stacks 02ZF;
* `CategoryTheory.Functor.isEquivalence_toDescentData_of_isStack`, its forward direction for a
  covering family indexed by a type in an arbitrary universe;
* `CategoryTheory.Functor.isStack_pullbackPseudofunctor_iff`, that a fibred category is a stack in
  the sense of Stacks 026F exactly when its pullback pseudofunctor is a stack in Mathlib's sense.

## Implementation notes

The descent data of `CategoryTheory.Functor.SieveDescentDatum` are indexed by the arrows of a sieve
and those of `CategoryTheory.Pseudofunctor.DescentData` by the members of a family, and the two
carry the same gluing data — an isomorphism for each pair of morphisms into two of the sources
agreeing over the base, with the cocycle condition and compatibility with base change. So for the
family consisting of all arrows of a covering sieve the two notions correspond, and the
correspondence is used only on objects: `SieveDescentDatum.toFamily` transports a datum, and
effectivity of a datum is matched with membership in the essential image of `toDescentData`
(`SieveDescentDatum.isEffective_of_iso_toFamily` and
`SieveDescentDatum.exists_iso_toDescentData_of_isEffective_ofFamily`). No functoriality of the
correspondence is needed, which is why it is not set up as an equivalence of categories, and
neither reading is applied to the output of the other — the two are inverse to each other only up
to the name of the morphism to the base that a pair of gluing morphisms lies over
(`descentData_hom_congr_base`) and up to `SieveDescentDatum.iso_symm`.

The dictionary between the pullback pseudofunctor and the chosen pullbacks of `p` is the group of
lemmas `pullbackPseudofunctor_map_map`, `pullbackPseudofunctor_mapComp'_hom_app` and
`pullbackPseudofunctor_mapComp'_inv_app`: the pullback functors of the pseudofunctor act on
morphisms of a fibre by `CategoryTheory.Functor.pullbackFiberHom`, and its compositors are the
canonical contractions `CategoryTheory.Functor.pullbackFiberCompIso'` of iterated chosen pullbacks.
Every identification below is a consequence of those three and of the uniqueness of a morphism into
a chosen cartesian lift.

## References

* [Stacks Project, Tag 02ZF](https://stacks.math.columbia.edu/tag/02ZF)
-/

@[expose] public section

-- The chosen pullbacks and the inclusion of a fibre are semireducible, so the endpoints of the
-- composites below agree only once they unfold.
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.Functor

open Opposite IsFibered Pseudofunctor

universe w v₁ v₂ u₁ u₂

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

/-! ### The dictionary between the pullback pseudofunctor and the chosen pullbacks -/

variable (p : 𝒳 ⥤ 𝒮) [p.IsFibered]

/-- The pullback functor of the pullback pseudofunctor along `f` acts on a morphism of a fibre by
base change along `f`. -/
lemma pullbackPseudofunctor_map_map {U V : 𝒮} (f : V ⟶ U) {x y : p.Fiber U} (α : x ⟶ y) :
    ((pullbackPseudofunctor p).map f.op.toLoc).toFunctor.map α = pullbackFiberHom α f :=
  pullbackFiberHom_uniq α f _ (fiberPullbackMap_comm f α)

/-- The compositor of the pullback pseudofunctor at `f` and `ε`, read at a *named* morphism `q`
that the composite `ε ≫ f` equals, is the canonical contraction of the iterated chosen pullback.
-/
lemma pullbackPseudofunctor_mapComp'_hom_app {U V Z : 𝒮} (f : V ⟶ U) (ε : Z ⟶ V) (q : Z ⟶ U)
    (hq : ε ≫ f = q) (x : p.Fiber U) :
    ((pullbackPseudofunctor p).mapComp' f.op.toLoc ε.op.toLoc q.op.toLoc
        (by rw [← hq]; rfl)).hom.toNatTrans.app x =
      (pullbackFiberCompIso' x f ε q hq).inv := by
  subst hq
  simp only [op_comp, Quiver.Hom.comp_toLoc]
  rw [mapComp'_eq_mapComp, pullbackFiberCompIso'_rfl]
  refine fiber_hom_ext_of_cartesian (p := p) (ε ≫ f)
    (IsPreFibered.pullbackMap (pullbackFiber p x f).2 ε ≫ IsPreFibered.pullbackMap x.2 f)
    (isCartesian_pullbackMap_comp_pullbackMap x f ε (ε ≫ f) rfl) _ _ ?_
  rw [pullbackFiberCompIso_inv_fac]
  exact pullbackPseudofunctor_mapComp_compatible p f.op.toLoc ε.op.toLoc x

/-- The inverse form of `pullbackPseudofunctor_mapComp'_hom_app`. -/
lemma pullbackPseudofunctor_mapComp'_inv_app {U V Z : 𝒮} (f : V ⟶ U) (ε : Z ⟶ V) (q : Z ⟶ U)
    (hq : ε ≫ f = q) (x : p.Fiber U) :
    ((pullbackPseudofunctor p).mapComp' f.op.toLoc ε.op.toLoc q.op.toLoc
        (by rw [← hq]; rfl)).inv.toNatTrans.app x =
      (pullbackFiberCompIso' x f ε q hq).hom := by
  have h2 : ((pullbackPseudofunctor p).mapComp' f.op.toLoc ε.op.toLoc q.op.toLoc
      (by rw [← hq]; rfl)).hom.toNatTrans.app x ≫
      ((pullbackPseudofunctor p).mapComp' f.op.toLoc ε.op.toLoc q.op.toLoc
      (by rw [← hq]; rfl)).inv.toNatTrans.app x = 𝟙 _ := by
    rw [← Cat.Hom₂.comp_app, Iso.hom_inv_id]
    rfl
  rw [pullbackPseudofunctor_mapComp'_hom_app p f ε q hq x] at h2
  simpa using (Iso.inv_comp_eq _).1 h2

/-- Contracting an iterated chosen pullback and expanding it again along a second morphism with the
same composite is the canonical comparison of the two chosen pullbacks. -/
lemma pullbackFiberCompIso'_hom_comp_inv {U V W Z : 𝒮} (x : p.Fiber U) (f : V ⟶ U) (g : W ⟶ U)
    (ε : Z ⟶ V) (ε' : Z ⟶ W) (q : Z ⟶ U) (hf : ε ≫ f = q) (hg : ε' ≫ g = q)
    (heq : ε ≫ f = ε' ≫ g) :
    (pullbackFiberCompIso' x f ε q hf).hom ≫ (pullbackFiberCompIso' x g ε' q hg).inv =
      (pullbackFiberComparison x ε ε' heq).hom := by
  subst hf
  refine fiber_hom_ext_of_cartesian (p := p) (ε ≫ f)
    (IsPreFibered.pullbackMap (pullbackFiber p x g).2 ε' ≫ IsPreFibered.pullbackMap x.2 g)
    (isCartesian_pullbackMap_comp_pullbackMap x g ε' (ε ≫ f) hg) _ _ ?_
  rw [Functor.map_comp, Category.assoc, pullbackFiberCompIso'_inv_fac,
    pullbackFiberCompIso'_hom_fac]
  exact (pullbackFiberComparison_hom_fac x ε ε' heq).symm

/-- Mathlib's pullback of a morphism between two chosen pullbacks along a further morphism of the
base is base change, conjugated by the canonical contractions of the iterated chosen pullbacks. -/
lemma pullHom_eq {V W Z Z' : 𝒮} (a : p.Fiber V) (b : p.Fiber W) (ε : Z ⟶ V) (ε' : Z ⟶ W)
    (γ : Z' ⟶ Z) (φ : pullbackFiber p a ε ⟶ pullbackFiber p b ε') :
    LocallyDiscreteOpToCat.pullHom (F := pullbackPseudofunctor p) (M₁ := a) (M₂ := b) (f₁ := ε)
        (f₂ := ε') φ γ (γ ≫ ε) (γ ≫ ε') rfl rfl =
      (pullbackFiberCompIso a ε γ).inv ≫ pullbackFiberHom φ γ ≫
        (pullbackFiberCompIso b ε' γ).hom := by
  dsimp only [LocallyDiscreteOpToCat.pullHom]
  rw [pullbackPseudofunctor_mapComp'_hom_app p ε γ (γ ≫ ε) rfl,
    pullbackPseudofunctor_mapComp'_inv_app p ε' γ (γ ≫ ε') rfl,
    pullbackPseudofunctor_map_map, pullbackFiberCompIso'_rfl, pullbackFiberCompIso'_rfl]

/-! ### Condition (2): the presheaf of morphisms -/

/-- The restriction map of the presheaf of morphisms of the pullback pseudofunctor is the
restriction map `CategoryTheory.Functor.morRestrict` of the presheaf `Mor(x, y)` of Stacks 02ZB. -/
lemma presheafHom_map_eq_morRestrict {U : 𝒮} (x y : p.Fiber U) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂)
    (m : (morPresheaf p x y).obj (op g₂)) :
    ((pullbackPseudofunctor p).presheafHom x y).map h.op m = (morPresheaf p x y).map h.op m := by
  dsimp [Pseudofunctor.presheafHom, LocallyDiscreteOpToCat.pullHom]
  rw [pullbackPseudofunctor_mapComp'_hom_app p g₂.hom h.left g₁.hom (Over.w h),
    pullbackPseudofunctor_mapComp'_inv_app p g₂.hom h.left g₁.hom (Over.w h),
    pullbackPseudofunctor_map_map]
  exact (morRestrict_eq_pullbackFiberHom p x y h m).symm

/-- The presheaf `Mor(x, y)` of Stacks 02ZB is the presheaf of morphisms of the pullback
pseudofunctor: both have the morphisms `f^* x ⟶ f^* y` of a fibre as sections over `f`, and their
restriction maps agree by `CategoryTheory.Functor.morRestrict_eq_pullbackFiberHom`. -/
noncomputable def morPresheafIso {U : 𝒮} (x y : p.Fiber U) :
    morPresheaf p x y ≅ (pullbackPseudofunctor p).presheafHom x y :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    rintro ⟨g₂⟩ ⟨g₁⟩ ⟨h⟩
    ext m
    exact (presheafHom_map_eq_morRestrict p x y h m).symm)

/-- Condition (2) of Stacks 026F for `p` is Mathlib's prestack condition for the pullback
pseudofunctor. -/
theorem isPrestack_pullbackPseudofunctor_iff (J : GrothendieckTopology 𝒮) :
    (pullbackPseudofunctor p).IsPrestack J ↔ ∀ (U : 𝒮) (x y : p.Fiber U), IsMorSheaf p J U x y := by
  refine ⟨fun h U x y => ?_,
    fun h => ⟨fun {_} x y => (Presheaf.isSheaf_of_iso_iff (morPresheafIso p x y)).1 (h _ x y)⟩⟩
  exact (Presheaf.isSheaf_of_iso_iff (morPresheafIso p x y)).2
    (Pseudofunctor.IsPrestack.isSheaf (F := pullbackPseudofunctor p) J
      (M := (x : (pullbackPseudofunctor p).obj ⟨op U⟩)) (N := y))

/-! ### Condition (3): descent data relative to a covering sieve

The descent data of a covering sieve `R` in the sense of
`CategoryTheory.Functor.SieveDescentDatum` are the descent data, in Mathlib's sense, relative to
the covering family consisting of *all* arrows of `R`. -/

/-- The gluing morphisms of a descent datum do not depend on the name of the morphism to the base
that the two composites equal. -/
lemma descentData_hom_congr_base {U : 𝒮} {ι : Type w} {X : ι → 𝒮}
    {fam : ∀ i, X i ⟶ U} (D : (pullbackPseudofunctor p).DescentData fam) {Y : 𝒮} (q q' : Y ⟶ U)
    {i₁ i₂ : ι} (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (h₁ : f₁ ≫ fam i₁ = q) (h₂ : f₂ ≫ fam i₂ = q)
    (h₁' : f₁ ≫ fam i₁ = q') (h₂' : f₂ ≫ fam i₂ = q') :
    D.hom q f₁ f₂ h₁ h₂ = D.hom q' f₁ f₂ h₁' h₂' := by
  obtain rfl : q = q' := h₁.symm.trans h₁'
  rfl

/-- The canonical descent datum of an object of the fibre, in Mathlib's sense, glues the chosen
pullbacks by the canonical comparisons `CategoryTheory.Functor.pullbackFiberComparison`. -/
lemma toDescentData_obj_hom {U : 𝒮} {ι : Type w} {X : ι → 𝒮} (fam : ∀ i, X i ⟶ U) (x : p.Fiber U)
    {Y : 𝒮} (q : Y ⟶ U) {i₁ i₂ : ι} (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ fam i₁ = q) (hf₂ : f₂ ≫ fam i₂ = q) (heq : f₁ ≫ fam i₁ = f₂ ≫ fam i₂) :
    (((pullbackPseudofunctor p).toDescentData fam).obj x).hom q f₁ f₂ hf₁ hf₂ =
      (pullbackFiberComparison x f₁ f₂ heq).hom := by
  dsimp [Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj]
  rw [pullbackPseudofunctor_mapComp'_inv_app p (fam i₁) f₁ q hf₁,
    pullbackPseudofunctor_mapComp'_hom_app p (fam i₂) f₂ q hf₂,
    pullbackFiberCompIso'_hom_comp_inv p x (fam i₁) (fam i₂) f₁ f₂ q hf₁ hf₂ heq]

namespace SieveDescentDatum

variable {p} {U : 𝒮} {R : Sieve U}

/-- A descent datum relative to a covering sieve `R`, read as a descent datum relative to the
covering family consisting of all arrows of `R`. -/
noncomputable def toFamily (D : SieveDescentDatum p R) :
    (pullbackPseudofunctor p).DescentData (fun (i : R.arrows.category) => i.obj.hom) where
  obj i := D.obj i.obj.hom i.property
  hom _ _ i₁ i₂ f₁ f₂ hf₁ hf₂ := (D.iso i₁.property i₂.property f₁ f₂ (by rw [hf₁, hf₂])).hom
  pullHom_hom _ _ g _ _ _ i₁ i₂ f₁ f₂ hf₁ hf₂ _ _ hgf₁ hgf₂ := by
    subst hgf₁
    subst hgf₂
    exact (pullHom_eq p _ _ f₁ f₂ g _).trans
      (D.iso_pullback i₁.property i₂.property f₁ f₂ (by rw [hf₁, hf₂]) g)
  hom_self _ _ i g _ := D.iso_self i.property g _
  hom_comp _ _ i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ :=
    D.cocycle i₁.property i₂.property i₃.property f₁ f₂ f₃ (by rw [hf₁, hf₂]) (by rw [hf₂, hf₃])
      (by rw [hf₁, hf₃])

/-- A descent datum relative to the covering family consisting of all arrows of a sieve `R`, read
as a descent datum relative to `R`. -/
noncomputable def ofFamily
    (D : (pullbackPseudofunctor p).DescentData (fun (i : R.arrows.category) => i.obj.hom)) :
    SieveDescentDatum p R where
  obj {_V} f hf := D.obj (R.arrows.categoryMk f hf)
  iso {_V _W _Z} {f} hf {g} hg ε ε' heq :=
    D.iso (i₁ := R.arrows.categoryMk f hf) (i₂ := R.arrows.categoryMk g hg) (ε ≫ f) ε ε' rfl
      heq.symm
  cocycle {_V _W _X _Z} {f} hf {g} hg {h} hh ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃ := by
    refine Eq.trans (congrArg (fun z => (D.hom (i₁ := R.arrows.categoryMk f hf)
        (i₂ := R.arrows.categoryMk g hg) (ε₁ ≫ f) ε₁ ε₂ rfl h₁₂.symm) ≫ z)
      (descentData_hom_congr_base p D (i₁ := R.arrows.categoryMk g hg)
        (i₂ := R.arrows.categoryMk h hh) (ε₂ ≫ g) (ε₁ ≫ f) ε₂ ε₃ rfl h₂₃.symm h₁₂.symm
        h₁₃.symm)) ?_
    exact D.hom_comp (i₁ := R.arrows.categoryMk f hf) (i₂ := R.arrows.categoryMk g hg)
      (i₃ := R.arrows.categoryMk h hh) (ε₁ ≫ f) ε₁ ε₂ ε₃ rfl h₁₂.symm h₁₃.symm
  iso_pullback {_V _W _Z _Z'} {f} hf {g} hg ε ε' heq γ :=
    (pullHom_eq p (D.obj (R.arrows.categoryMk f hf)) (D.obj (R.arrows.categoryMk g hg)) ε ε' γ
      (D.hom (i₁ := R.arrows.categoryMk f hf) (i₂ := R.arrows.categoryMk g hg) (ε ≫ f) ε ε' rfl
        heq.symm)).symm.trans
      (D.pullHom_hom (i₁ := R.arrows.categoryMk f hf) (i₂ := R.arrows.categoryMk g hg) γ (ε ≫ f)
        ((γ ≫ ε) ≫ f) (Category.assoc γ ε f).symm ε ε' rfl heq.symm (γ ≫ ε) (γ ≫ ε') rfl rfl)

/-- If the canonical descent datum of an object of the fibre over `U` is isomorphic, as a descent
datum relative to the family of all arrows of a sieve `R`, to a descent datum relative to `R`, then
that datum is effective: the components of the isomorphism, followed by the chosen cartesian lifts
of the object, are the required cartesian morphisms. -/
lemma isEffective_of_iso_toFamily (D : SieveDescentDatum p R) (x : p.Fiber U)
    (α : ((pullbackPseudofunctor p).toDescentData
      (fun (i : R.arrows.category) => i.obj.hom)).obj x ≅ D.toFamily) : D.IsEffective := by
  have hinv : ∀ i, IsIso (α.inv.hom i) := fun i =>
    ⟨α.hom.hom i, by rw [← Pseudofunctor.DescentData.comp_hom, α.inv_hom_id,
        Pseudofunctor.DescentData.id_hom],
      by rw [← Pseudofunctor.DescentData.comp_hom, α.hom_inv_id,
        Pseudofunctor.DescentData.id_hom]⟩
  refine ⟨x, fun {V} f hf => Fiber.fiberInclusion.map (α.inv.hom (R.arrows.categoryMk f hf)) ≫
    IsPreFibered.pullbackMap x.2 f, fun {V} f hf => ?_, fun {V W Z} {f} hf {g} hg ε ε' heq => ?_⟩
  · have := hinv (R.arrows.categoryMk f hf)
    have : p.IsHomLift (𝟙 V) (Fiber.fiberInclusion.map (α.inv.hom (R.arrows.categoryMk f hf))) :=
      (α.inv.hom (R.arrows.categoryMk f hf)).2
    have : p.IsCartesian f (IsPreFibered.pullbackMap x.2 f) :=
      IsPreFibered.pullbackMap.IsCartesian x.2 f
    have h : p.IsCartesian (𝟙 V ≫ f)
        (Fiber.fiberInclusion.map (α.inv.hom (R.arrows.categoryMk f hf)) ≫
          IsPreFibered.pullbackMap x.2 f) := inferInstance
    rwa [Category.id_comp] at h
  · have hc := α.inv.comm (i₁ := R.arrows.categoryMk f hf) (i₂ := R.arrows.categoryMk g hg)
      (ε ≫ f) ε ε' rfl heq.symm
    rw [pullbackPseudofunctor_map_map, pullbackPseudofunctor_map_map,
      toDescentData_obj_hom p (fun (i : R.arrows.category) => i.obj.hom) x
        (i₁ := R.arrows.categoryMk f hf) (i₂ := R.arrows.categoryMk g hg) (ε ≫ f) ε ε' rfl
        heq.symm heq] at hc
    have h2 := congrArg Fiber.fiberInclusion.map hc =≫
      (IsPreFibered.pullbackMap (pullbackFiber p x g).2 ε' ≫ IsPreFibered.pullbackMap x.2 g)
    simp only [Functor.map_comp, Category.assoc] at h2
    have key : Fiber.fiberInclusion.map (pullbackFiberComparison x ε ε' heq).hom ≫
        IsPreFibered.pullbackMap (pullbackFiber p x g).2 ε' ≫ IsPreFibered.pullbackMap x.2 g =
          IsPreFibered.pullbackMap (pullbackFiber p x f).2 ε ≫ IsPreFibered.pullbackMap x.2 f :=
      pullbackFiberComparison_hom_fac x ε ε' heq
    rw [key, pullbackFiberHom_fac_assoc, pullbackFiberHom_fac_assoc] at h2
    exact h2.symm

/-- If a descent datum relative to the family of all arrows of a sieve `R` is effective when read
as a descent datum relative to `R`, it is isomorphic to the canonical descent datum of the object
it descends to. -/
lemma exists_iso_toDescentData_of_isEffective_ofFamily
    (D : (pullbackPseudofunctor p).DescentData (fun (i : R.arrows.category) => i.obj.hom))
    (hD : (ofFamily D).IsEffective) :
    ∃ x : p.Fiber U, Nonempty (((pullbackPseudofunctor p).toDescentData
      (fun (i : R.arrows.category) => i.obj.hom)).obj x ≅ D) := by
  obtain ⟨x, ζ, hcart, hcompat⟩ := hD
  refine ⟨x, ⟨Pseudofunctor.DescentData.isoMk (fun i => fiberIsoOfCartesian i.obj.hom
    (IsPreFibered.pullbackMap x.2 i.obj.hom) (ζ i.obj.hom i.property)
    (IsPreFibered.pullbackMap.IsCartesian _ _) (hcart i.obj.hom i.property)) ?_⟩⟩
  intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
  rw [pullbackPseudofunctor_map_map, pullbackPseudofunctor_map_map,
    toDescentData_obj_hom p (fun (i : R.arrows.category) => i.obj.hom) x (i₁ := i₁) (i₂ := i₂)
      q f₁ f₂ hf₁ hf₂ (by rw [hf₁, hf₂]),
    descentData_hom_congr_base p D (i₁ := i₁) (i₂ := i₂) q (f₁ ≫ i₁.obj.hom) f₁ f₂ hf₁ hf₂ rfl
      (by rw [hf₂, ← hf₁])]
  refine fiber_hom_ext_of_cartesian (p := p) q
    (IsPreFibered.pullbackMap (D.obj i₂).2 f₂ ≫ ζ i₂.obj.hom i₂.property) ?_ _ _ ?_
  · have : p.IsCartesian f₂ (IsPreFibered.pullbackMap (D.obj i₂).2 f₂) :=
      IsPreFibered.pullbackMap.IsCartesian _ _
    have : p.IsCartesian i₂.obj.hom (ζ i₂.obj.hom i₂.property) := hcart i₂.obj.hom i₂.property
    have h : p.IsCartesian (f₂ ≫ i₂.obj.hom)
        (IsPreFibered.pullbackMap (D.obj i₂).2 f₂ ≫ ζ i₂.obj.hom i₂.property) := inferInstance
    rwa [hf₂] at h
  · have hcp : Fiber.fiberInclusion.map (D.hom (i₁ := i₁) (i₂ := i₂) (f₁ ≫ i₁.obj.hom) f₁ f₂ rfl
          (by rw [hf₂, ← hf₁])) ≫
        IsPreFibered.pullbackMap (D.obj i₂).2 f₂ ≫ ζ i₂.obj.hom i₂.property =
          IsPreFibered.pullbackMap (D.obj i₁).2 f₁ ≫ ζ i₁.obj.hom i₁.property :=
      hcompat i₁.property i₂.property f₁ f₂ (by rw [hf₁, hf₂])
    simp only [Functor.map_comp, Category.assoc]
    rw [hcp]
    simp [pullbackFiberHom_fac_assoc, fiberIsoOfCartesian_hom_fac,
      pullbackFiberComparison_hom_fac]

end SieveDescentDatum

/-! ### Stacks 02ZF -/

/-- Condition (3) of Stacks 026F makes the functor from the fibre over `U` to the descent data
relative to the family of all arrows of a covering sieve of `U` essentially surjective. -/
theorem essSurj_toDescentData_of_hasEffectiveDescent {J : GrothendieckTopology 𝒮}
    (hdesc : HasEffectiveDescent p J) {U : 𝒮} (R : Sieve U) (hR : R ∈ J U) :
    ((pullbackPseudofunctor p).toDescentData
      (fun (i : R.arrows.category) => i.obj.hom)).EssSurj := by
  refine ⟨fun D => ?_⟩
  obtain ⟨x, hx⟩ := SieveDescentDatum.exists_iso_toDescentData_of_isEffective_ofFamily D
    (hdesc R hR (SieveDescentDatum.ofFamily D))
  exact ⟨x, hx⟩

/-- `p` is a stack in the sense of Stacks 026F exactly when its pullback pseudofunctor is a stack
in Mathlib's sense. Condition (2) of Stacks 026F is Mathlib's prestack condition by
`isPrestack_pullbackPseudofunctor_iff`, and condition (3) is essential surjectivity of the functors
to the categories of descent data of covering sieves. -/
theorem isStack_pullbackPseudofunctor_iff (J : GrothendieckTopology 𝒮) :
    (pullbackPseudofunctor p).IsStack J ↔ p.IsStack J := by
  constructor
  · intro _
    exact { isFibered := inferInstance
            isMorSheaf := (isPrestack_pullbackPseudofunctor_iff p J).1 inferInstance
            hasEffectiveDescent := fun {U} R hR D =>
              have := Pseudofunctor.IsStack.essSurj_of_sieve (pullbackPseudofunctor p) R hR
              SieveDescentDatum.isEffective_of_iso_toFamily D _
                (Functor.objObjPreimageIso _ D.toFamily) }
  · intro hp
    have : (pullbackPseudofunctor p).IsPrestack J :=
      (isPrestack_pullbackPseudofunctor_iff p J).2 hp.isMorSheaf
    exact { essSurj_of_sieve := fun R hR =>
      essSurj_toDescentData_of_hasEffectiveDescent p hp.hasEffectiveDescent R hR }

/-- **Stacks 02ZF.** Let `p : 𝒳 ⥤ 𝒮` be a fibred category over a site `(𝒮, J)`. Then `p` is a stack
if and only if, for every covering `𝒰 = {f i : U i ⟶ U}` of the site, the functor `𝒳_U ⥤ DD(𝒰)`
sending an object of the fibre over `U` to its canonical descent datum relative to `𝒰` is an
equivalence. -/
@[stacks 02ZF]
theorem isStack_iff_isEquivalence_toDescentData (J : GrothendieckTopology 𝒮) :
    p.IsStack J ↔ ∀ ⦃U : 𝒮⦄ (𝒰 : PreZeroHypercover.{max u₁ v₁} U), 𝒰.sieve₀ ∈ J U →
      ((pullbackPseudofunctor p).toDescentData 𝒰.f).IsEquivalence := by
  constructor
  · intro hp U 𝒰 h𝒰
    have := (isStack_pullbackPseudofunctor_iff p J).2 hp
    exact Pseudofunctor.isEquivalence_toDescentData _ 𝒰.f h𝒰
  · intro h
    refine (isStack_pullbackPseudofunctor_iff p J).1 (Pseudofunctor.IsStack.of_isStackFor
      (fun S R hR => ⟨h ⟨R.arrows.category, fun i => i.obj.left, fun i => i.obj.hom⟩ ?_⟩))
    have heq : (PreZeroHypercover.mk (S := S) R.arrows.category (fun i => i.obj.left)
        (fun i => i.obj.hom)).sieve₀ = R := Sieve.ofArrows_category R
    rw [heq]
    exact hR

/-- **Stacks 02ZF**, the implication (1) ⟹ (2) for a covering family indexed by a type in an
arbitrary universe. The right hand side of `isStack_iff_isEquivalence_toDescentData` quantifies
over the families indexed by a type in `Type (max u₁ v₁)`, which is no restriction on the
*condition* because every covering sieve is generated by such a family
(`CategoryTheory.Sieve.exists_eq_ofArrows`), but does restrict the implication read on its own. -/
theorem isEquivalence_toDescentData_of_isStack {J : GrothendieckTopology 𝒮} (hp : p.IsStack J)
    {U : 𝒮} {ι : Type w} {X : ι → 𝒮} (f : ∀ i, X i ⟶ U) (hf : Sieve.ofArrows X f ∈ J U) :
    ((pullbackPseudofunctor p).toDescentData f).IsEquivalence :=
  have := (isStack_pullbackPseudofunctor_iff p J).2 hp
  Pseudofunctor.isEquivalence_toDescentData _ f hf

end CategoryTheory.Functor


