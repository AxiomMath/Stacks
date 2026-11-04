module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Stack
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.SliceOverMap
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.Dictionary
public import StacksFrontier.CategoryTheory.TwoFibreProductOverRelocalize
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Subcanonical

/-!
# Restrictions and a change of slice

Let `g : V ⟶ W` be a morphism of a category `𝒞` and let `p : 𝒮 ⥤ 𝒞/V` be a category over the
slice at `V`. Composing with `CategoryTheory.Over.map g` makes `𝒮` a category over the slice at
`W`. This file transfers restrictions (`CategoryTheory.Functor.Restriction`), the fibre-morphism
condition (`CategoryTheory.Functor.FibreHom`) and the canonical-restriction relation
(`CategoryTheory.Functor.IsRestrictionOf`) between `p` and `p ⋙ Over.map g`, and shows that, for
a subcanonical topology, `p` is a stack in groupoids for the localized topology at `V` exactly
when `p ⋙ Over.map g` is one for the localized topology at `W`.

## Main definitions

* `CategoryTheory.Over.mapDescend`: the preimage under `Over.map g` of a morphism between
  objects of its image which is compatible with the structure morphisms to `V`.
* `CategoryTheory.Functor.Restriction.overMap` and
  `CategoryTheory.Functor.Restriction.ofOverMap`: the two directions of the correspondence of
  restrictions, each keeping the restricting object and the cartesian morphism unchanged.
* `CategoryTheory.Functor.Restriction.ofEq`: a restriction read along an equal base morphism.
* `CategoryTheory.Functor.Restriction.descend` and
  `CategoryTheory.Functor.Restriction.toOverMap`: the same two directions, along a given base
  morphism on each side rather than one in the image of `Over.map g`.

## Main results

* `CategoryTheory.Over.isPullback_iff_left` and `CategoryTheory.Over.isPullback_map_iff`: a
  square of a slice category is a pullback exactly when its square of underlying morphisms is,
  so a change of slice neither creates nor destroys pullbacks.
* `CategoryTheory.Functor.isHomLift_overMap_iff` and
  `CategoryTheory.Functor.isStronglyCartesian_overMap_iff`: lying over a morphism, and being
  strongly cartesian over it, are unchanged by the change of slice, once the two objects of
  `𝒞/V` that the morphism of `𝒮` lies over are known.
* `CategoryTheory.Functor.compTo_overMap`: the canonical comparison of two restrictions is the
  same morphism of `𝒮` on both sides.
* `CategoryTheory.Functor.fibreHom_overMap_iff` and
  `CategoryTheory.Functor.isRestrictionOf_overMap_iff`: the fibre-morphism condition and the
  canonical-restriction relation are unchanged.
* `CategoryTheory.Over.eq_of_mem_over` and
  `CategoryTheory.Over.exists_factorization_of_mem_over`: for a subcanonical topology a covering
  family of a slice object is jointly epimorphic, and a compatible family of factorizations of
  the structure morphisms through `g` glues.
* `CategoryTheory.Functor.obj_eq_of_fibreHom_overMap`: two objects of `𝒞/V` under objects of
  `𝒮` joined by a morphism of a fibre of the changed slice are equal.
* `CategoryTheory.Over.isPullback_mk` and `CategoryTheory.Over.mem_over_mk`: re-basing the
  objects of a slice at `W` over `V`, along factorizations of their structure morphisms through
  `g`, preserves fibre-product squares and covering families of the localized topology.
* `CategoryTheory.Functor.isStackInGroupoids_of_comp_overMap` and
  `CategoryTheory.Functor.isStackInGroupoids_comp_overMap`: being a stack in groupoids over the
  slice at `W` and being one over the slice at `V` are equivalent.

## References

* [Stacks Project, Tag 02XK](https://stacks.math.columbia.edu/tag/02XK)
* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe w v₁ u₁ v₂ u₂

namespace Functor

variable {𝒟 : Type u₁} [Category.{v₁} 𝒟] {𝒮 : Type u₂} [Category.{v₂} 𝒮]

/-- **A restriction read along an equal base morphism.** The restricting object and the cartesian
morphism are unchanged; only the two conditions on them are transported, along the identifications
of the source and of the target of the base morphism. -/
@[implicit_reducible]
def Restriction.ofEq (p : 𝒮 ⥤ 𝒟) {A D A' D' : 𝒟} {f : A ⟶ D} {f' : A' ⟶ D'}
    (eA : A = A') (eD : D = D') (hf : f' = eqToHom eA.symm ≫ f ≫ eqToHom eD)
    {x : 𝒮} {hx : p.obj x = D} (hx' : p.obj x = D')
    (xr : Restriction p f x hx) : Restriction p f' x hx' where
  pt := xr.pt
  hpt := xr.hpt.trans eA
  hom := xr.hom
  isHomLift := by
    subst eA; subst eD; subst hf
    simpa using xr.isHomLift
  isCart := by
    subst eA; subst eD; subst hf
    simpa using xr.isCart

/-- Reading a restriction along an equal base morphism keeps its restricting object. -/
@[simp]
lemma Restriction.ofEq_pt (p : 𝒮 ⥤ 𝒟) {A D A' D' : 𝒟} {f : A ⟶ D} {f' : A' ⟶ D'}
    (eA : A = A') (eD : D = D') (hf : f' = eqToHom eA.symm ≫ f ≫ eqToHom eD)
    {x : 𝒮} {hx : p.obj x = D} (hx' : p.obj x = D')
    (xr : Restriction p f x hx) : (xr.ofEq p eA eD hf hx').pt = xr.pt :=
  rfl

/-- Reading a restriction along an equal base morphism keeps its cartesian morphism. -/
@[simp]
lemma Restriction.ofEq_hom (p : 𝒮 ⥤ 𝒟) {A D A' D' : 𝒟} {f : A ⟶ D} {f' : A' ⟶ D'}
    (eA : A = A') (eD : D = D') (hf : f' = eqToHom eA.symm ≫ f ≫ eqToHom eD)
    {x : 𝒮} {hx : p.obj x = D} (hx' : p.obj x = D')
    (xr : Restriction p f x hx) : (xr.ofEq p eA eD hf hx').hom = xr.hom :=
  rfl

/-- **The canonical comparison of two restrictions is unchanged by reading them along equal base
morphisms.** -/
lemma compTo_ofEq (p : 𝒮 ⥤ 𝒟) [p.IsFibered] {A B D A' B' D' : 𝒟} (eA : A = A') (eB : B = B')
    (eD : D = D') {k : A ⟶ B} {f : B ⟶ D} {m : A ⟶ D} (hm : m = k ≫ f)
    {k' : A' ⟶ B'} {f' : B' ⟶ D'} {m' : A' ⟶ D'} (hm' : m' = k' ≫ f')
    (hk : k' = eqToHom eA.symm ≫ k ≫ eqToHom eB)
    (hf : f' = eqToHom eB.symm ≫ f ≫ eqToHom eD)
    (hmm : m' = eqToHom eA.symm ≫ m ≫ eqToHom eD)
    {x : 𝒮} {hx : p.obj x = D} (hx' : p.obj x = D')
    (xr : Restriction p f x hx) (xrA : Restriction p m x hx) :
    Restriction.compTo p k' f' hm' (xr.ofEq p eB eD hf hx') (xrA.ofEq p eA eD hmm hx') =
      Restriction.compTo p k f hm xr xrA := by
  refine (Restriction.eq_compTo k' f' hm' (xr.ofEq p eB eD hf hx') (xrA.ofEq p eA eD hmm hx')
    (Restriction.compTo p k f hm xr xrA) ?_ (Restriction.compTo_hom p k f hm xr xrA)).symm
  rw [hk, IsHomLift.lift_eqToHom_comp_iff, IsHomLift.lift_comp_eqToHom_iff]
  exact Restriction.isHomLift_compTo k f hm xr xrA

/-- **The canonical-restriction relation is unchanged by reading the restrictions along equal base
morphisms.** -/
lemma isRestrictionOf_ofEq (p : 𝒮 ⥤ 𝒟) [p.IsFibered]
    {A D Bx By A' D' Bx' By' : 𝒟} (eA : A = A') (eD : D = D') (eBx : Bx = Bx') (eBy : By = By')
    {k : A ⟶ D} {fx : D ⟶ Bx} {fy : D ⟶ By} {mx : A ⟶ Bx} {my : A ⟶ By}
    (hfx : mx = k ≫ fx) (hfy : my = k ≫ fy)
    {k' : A' ⟶ D'} {fx' : D' ⟶ Bx'} {fy' : D' ⟶ By'} {mx' : A' ⟶ Bx'} {my' : A' ⟶ By'}
    (hfx' : mx' = k' ≫ fx') (hfy' : my' = k' ≫ fy')
    (hk : k' = eqToHom eA.symm ≫ k ≫ eqToHom eD)
    (hfxe : fx' = eqToHom eD.symm ≫ fx ≫ eqToHom eBx)
    (hfye : fy' = eqToHom eD.symm ≫ fy ≫ eqToHom eBy)
    (hmxe : mx' = eqToHom eA.symm ≫ mx ≫ eqToHom eBx)
    (hmye : my' = eqToHom eA.symm ≫ my ≫ eqToHom eBy)
    {x y : 𝒮} {hx : p.obj x = Bx} {hy : p.obj y = By}
    (hx' : p.obj x = Bx') (hy' : p.obj y = By')
    (xr : Restriction p fx x hx) (yr : Restriction p fy y hy)
    (xrA : Restriction p mx x hx) (yrA : Restriction p my y hy)
    (α : xr.pt ⟶ yr.pt) (β : xrA.pt ⟶ yrA.pt) :
    IsRestrictionOf p k' hfx' hfy' (xr.ofEq p eD eBx hfxe hx') (yr.ofEq p eD eBy hfye hy')
        (xrA.ofEq p eA eBx hmxe hx') (yrA.ofEq p eA eBy hmye hy') α β ↔
      IsRestrictionOf p k hfx hfy xr yr xrA yrA α β := by
  rw [show IsRestrictionOf p k hfx hfy xr yr xrA yrA α β =
      (β ≫ Restriction.compTo p k fy hfy yr yrA =
        Restriction.compTo p k fx hfx xr xrA ≫ α) from rfl,
    ← compTo_ofEq p eA eD eBy hfy hfy' hk hfye hmye hy' yr yrA,
    ← compTo_ofEq p eA eD eBx hfx hfx' hk hfxe hmxe hx' xr xrA]

/-- The fibre-morphism condition does not depend on which object of the base the two objects are
recorded as lying over. -/
lemma fibreHom_congr (p : 𝒮 ⥤ 𝒟) {U U' : 𝒟} {a b : 𝒮} (ha : p.obj a = U) (hb : p.obj b = U)
    (ha' : p.obj a = U') (hb' : p.obj b = U') (φ : a ⟶ b) :
    FibreHom p a b ha hb φ ↔ FibreHom p a b ha' hb' φ := by
  simp only [FibreHom, eqToHom_trans]

end Functor

namespace Over

variable {C : Type u₁} [Category.{v₁} C] {V W : C}

/-- `CategoryTheory.Over.map` is faithful. -/
instance faithful_map (g : V ⟶ W) : (Over.map g).Faithful where
  map_injective h := Over.OverMorphism.ext (by
    simpa only [Over.map_map_left] using congrArg Over.Hom.left h)

/-- **The preimage of a morphism under a change of slice.** A morphism of `𝒞/W` between the
images of two objects `A` and `B` of `𝒞/V` whose underlying morphism of `𝒞` is compatible with
the structure morphisms to `V`, as a morphism `A ⟶ B`. -/
def mapDescend (g : V ⟶ W) {A B : Over V} (k : (Over.map g).obj A ⟶ (Over.map g).obj B)
    (h : k.left ≫ B.hom = A.hom) : A ⟶ B :=
  Over.homMk k.left h

/-- The underlying morphism of `CategoryTheory.Over.mapDescend g k h` is that of `k`. -/
@[simp]
lemma mapDescend_left (g : V ⟶ W) {A B : Over V}
    (k : (Over.map g).obj A ⟶ (Over.map g).obj B) (h : k.left ≫ B.hom = A.hom) :
    (mapDescend g k h).left = k.left :=
  rfl

/-- `CategoryTheory.Over.mapDescend g k h` is a preimage of `k` under `Over.map g`. -/
@[simp]
lemma map_map_mapDescend (g : V ⟶ W) {A B : Over V}
    (k : (Over.map g).obj A ⟶ (Over.map g).obj B) (h : k.left ≫ B.hom = A.hom) :
    (Over.map g).map (mapDescend g k h) = k :=
  Over.OverMorphism.ext (by simp)

/-- A square of a slice category is a pullback exactly when the square of underlying morphisms
of the ambient category is. -/
lemma isPullback_iff_left {X : C} {A B₁ B₂ Y : Over X} (f₁ : A ⟶ B₁) (f₂ : A ⟶ B₂)
    (g₁ : B₁ ⟶ Y) (g₂ : B₂ ⟶ Y) (w : f₁ ≫ g₁ = f₂ ≫ g₂) :
    IsPullback f₁ f₂ g₁ g₂ ↔ IsPullback f₁.left f₂.left g₁.left g₂.left := by
  have _ := (inferInstance :
    PreservesLimitsOfShape WalkingCospan (Over.forget X)).preservesLimit (K := cospan g₁ g₂)
  have _ := (inferInstance :
    ReflectsLimitsOfShape WalkingCospan (Over.forget X)).reflectsLimit (K := cospan g₁ g₂)
  exact ⟨fun h => h.map (Over.forget X), fun h => IsPullback.of_map (Over.forget X) w h⟩

/-- A change of slice neither creates nor destroys pullback squares. -/
lemma isPullback_map_iff (g : V ⟶ W) {A B₁ B₂ Y : Over V} (f₁ : A ⟶ B₁) (f₂ : A ⟶ B₂)
    (g₁ : B₁ ⟶ Y) (g₂ : B₂ ⟶ Y) (w : f₁ ≫ g₁ = f₂ ≫ g₂) :
    IsPullback ((Over.map g).map f₁) ((Over.map g).map f₂) ((Over.map g).map g₁)
        ((Over.map g).map g₂) ↔ IsPullback f₁ f₂ g₁ g₂ := by
  rw [isPullback_iff_left f₁ f₂ g₁ g₂ w,
    isPullback_iff_left ((Over.map g).map f₁) ((Over.map g).map f₂) ((Over.map g).map g₁)
      ((Over.map g).map g₂) (by rw [← Functor.map_comp, ← Functor.map_comp, w])]
  simp only [Over.map_map_left]

/-- **The topology of a slice is unchanged by a change of slice.** A family of morphisms to `U`
in `𝒞/V` generates a covering sieve for the localized topology exactly when its image in `𝒞/W`
does. -/
@[sga "4 III 5.2" "special case"]
lemma mem_over_map_iff (J : GrothendieckTopology C) (g : V ⟶ W) {U : Over V} {I : Type w}
    (Z : I → Over V) (f : ∀ i, Z i ⟶ U) :
    Sieve.ofArrows (fun i => (Over.map g).obj (Z i)) (fun i => (Over.map g).map (f i))
        ∈ (J.over W) ((Over.map g).obj U) ↔ Sieve.ofArrows Z f ∈ (J.over V) U := by
  rw [GrothendieckTopology.mem_over_iff, GrothendieckTopology.mem_over_iff,
    Sieve.overEquiv_ofArrows, Sieve.overEquiv_ofArrows]
  simp only [Over.map_obj_left, Over.map_map_left]

/-- **A covering family of a slice is jointly epimorphic**, for a subcanonical topology: two
morphisms out of the base of the slice object which agree after composition with every member of
the family are equal. -/
lemma eq_of_mem_over (J : GrothendieckTopology C) [J.Subcanonical] {U : Over W} {I : Type w}
    (Z : I → Over W) (f : ∀ i, Z i ⟶ U) (hf : Sieve.ofArrows Z f ∈ (J.over W) U)
    {T : C} (a b : U.left ⟶ T) (hab : ∀ i, (f i).left ≫ a = (f i).left ≫ b) : a = b := by
  have hsh : Presieve.IsSheaf J (yoneda.obj T) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows] at hf
  refine (hsh _ hf).isSeparatedFor.ext ?_
  rintro Y h ⟨Y', u, v, ⟨i⟩, rfl⟩
  show (u ≫ (f i).left) ≫ a = (u ≫ (f i).left) ≫ b
  rw [Category.assoc, Category.assoc, hab i]

/-- **A compatible family of factorizations through `g` over a covering family glues.** For a
subcanonical topology, if the structure morphism of every member of a covering family of
`U : 𝒞/W` factors through `g : V ⟶ W` compatibly, then the structure morphism of `U` factors
through `g`, compatibly with the given factorizations. -/
lemma exists_factorization_of_mem_over (J : GrothendieckTopology C) [J.Subcanonical]
    (g : V ⟶ W) {U : Over W} {I : Type w} (Z : I → Over W) (f : ∀ i, Z i ⟶ U)
    (hf : Sieve.ofArrows Z f ∈ (J.over W) U)
    (a : ∀ i, (Z i).left ⟶ V) (ha : ∀ i, a i ≫ g = (Z i).hom)
    (hcompat : ∀ (i j : I) (Y : C) (u : Y ⟶ (Z i).left) (v : Y ⟶ (Z j).left),
      u ≫ (f i).left = v ≫ (f j).left → u ≫ a i = v ≫ a j) :
    ∃ c : U.left ⟶ V, c ≫ g = U.hom ∧ ∀ i, (f i).left ≫ c = a i := by
  have hsh : Presieve.IsSheaf J (yoneda.obj V) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  have hf' := hf
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows] at hf'
  have h1 : Presieve.IsSheafFor (yoneda.obj V)
      (Presieve.ofArrows (fun i => (Z i).left) (fun i => (f i).left)) :=
    (Presieve.isSheafFor_iff_generate _).2 (hsh _ hf')
  obtain ⟨c, hc, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 h1 a
    (fun i j Y u v huv => hcompat i j Y u v huv)
  have hc' : ∀ i, (f i).left ≫ c = a i := fun i => by simpa using hc i
  refine ⟨c, ?_, hc'⟩
  refine eq_of_mem_over J Z f hf (c ≫ g) U.hom fun i => ?_
  rw [← Category.assoc, hc' i, ha i, Over.w (f i)]

/-- Two objects of a slice category built from morphisms out of the same object of the ambient
category are equal only if those morphisms are. -/
lemma hom_eq_of_mk_eq {X : C} {a b : X ⟶ V} (h : (Over.mk a : Over V) = Over.mk b) : a = b := by
  simpa using (Over.w (eqToHom h : (Over.mk a : Over V) ⟶ Over.mk b)).symm

/-- Equal composites in a slice stay equal on underlying morphisms, followed by any `c`. -/
private lemma left_comp_comp_eq {A B B' T : Over W} {u : A ⟶ B} {v : A ⟶ B'} {f : B ⟶ T}
    {f' : B' ⟶ T} (h : u ≫ f = v ≫ f') (c : T.left ⟶ V) :
    u.left ≫ f.left ≫ c = v.left ≫ f'.left ≫ c := by
  have hw := congrArg Over.Hom.left h
  simp only [Over.comp_left] at hw
  simp only [← Category.assoc, hw]

/-- **A fibre-product square of a slice at `W` stays one after re-basing its objects over `V`.**
A square of `𝒞/V` between objects of the form `Over.mk _` whose morphisms have the same underlying
morphisms as those of a pullback square of `𝒞/W` is a pullback. -/
lemma isPullback_mk {Zi Zj Zij T : Over W}
    {fi : Zi ⟶ T} {fj : Zj ⟶ T} {p₁ : Zij ⟶ Zi} {p₂ : Zij ⟶ Zj} (hP : IsPullback p₁ p₂ fi fj)
    {aij : Zij.left ⟶ V} {ai : Zi.left ⟶ V} {aj : Zj.left ⟶ V} {c : T.left ⟶ V}
    (q₁ : (Over.mk aij : Over V) ⟶ Over.mk ai) (q₂ : (Over.mk aij : Over V) ⟶ Over.mk aj)
    (gi : (Over.mk ai : Over V) ⟶ Over.mk c) (gj : (Over.mk aj : Over V) ⟶ Over.mk c)
    (hq₁ : q₁.left = p₁.left) (hq₂ : q₂.left = p₂.left)
    (hgi : gi.left = fi.left) (hgj : gj.left = fj.left) :
    IsPullback q₁ q₂ gi gj := by
  have hPl := (Over.isPullback_iff_left p₁ p₂ fi fj hP.w).1 hP
  have hw : q₁ ≫ gi = q₂ ≫ gj := by
    refine Over.OverMorphism.ext ?_
    simp only [Over.comp_left, hq₁, hq₂, hgi, hgj]
    simpa using congrArg Over.Hom.left hP.w
  rwa [Over.isPullback_iff_left _ _ _ _ hw, hq₁, hq₂, hgi, hgj]

/-- **The localized topology does not see a re-basing of a covering family.** A covering family of
`U' : 𝒞/W` whose members and target are re-based over `V` along factorizations of their structure
morphisms through `g` is a covering family of the localized topology at `V`. -/
lemma mem_over_mk (J : GrothendieckTopology C) {U' : Over W} (c : U'.left ⟶ V)
    {I : Type w} (Z : I → Over W) (f : ∀ i, Z i ⟶ U')
    (hcov : Sieve.ofArrows Z f ∈ (J.over W) U') :
    Sieve.ofArrows (fun i => (Over.mk ((f i).left ≫ c) : Over V))
      (fun i => (Over.homMk (f i).left rfl :
        (Over.mk ((f i).left ≫ c) : Over V) ⟶ Over.mk c)) ∈ (J.over V) (Over.mk c) := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows] at hcov
  simpa using hcov

end Over

namespace Functor

variable {C : Type u₁} [Category.{v₁} C] {V W : C} {𝒮 : Type u₂} [Category.{v₂} 𝒮]
  (p : 𝒮 ⥤ Over V) (g : V ⟶ W)

/-- **Lying over a morphism is unchanged by a change of slice.** For a morphism `k` of `𝒞/V`
whose source and target are the images of the two objects of `𝒮` involved, a morphism of `𝒮`
lies over `k` exactly when it lies over `(Over.map g).map k` for the composite structure
functor. -/
lemma isHomLift_overMap_iff {a b : 𝒮} {A B : Over V} (k : A ⟶ B) (φ : a ⟶ b)
    (hA : p.obj a = A) (hB : p.obj b = B) :
    (p ⋙ Over.map g).IsHomLift ((Over.map g).map k) φ ↔ p.IsHomLift k φ := by
  refine ⟨fun h => ?_, fun h => isHomLift_comp_map p k φ h⟩
  have h' := h
  refine CategoryTheory.IsHomLift.of_fac' p k φ hA hB ?_
  refine (Over.map g).map_injective ?_
  have h2 := CategoryTheory.IsHomLift.fac' (p ⋙ Over.map g) ((Over.map g).map k) φ
  simpa only [Functor.comp_map, Functor.map_comp, eqToHom_map] using h2

/-- **Being strongly cartesian is preserved by a change of slice.** A morphism of `𝒮` which is
strongly cartesian over `k` for `p` is strongly cartesian over `(Over.map g).map k` for
`p ⋙ Over.map g`. -/
lemma isStronglyCartesian_overMap {a b : 𝒮} {A B : Over V} (k : A ⟶ B) (φ : a ⟶ b)
    (h : p.IsStronglyCartesian k φ) :
    (p ⋙ Over.map g).IsStronglyCartesian ((Over.map g).map k) φ := by
  have hl := h.toIsHomLift
  obtain rfl := CategoryTheory.IsHomLift.domain_eq p k φ
  obtain rfl := CategoryTheory.IsHomLift.codomain_eq p k φ
  have hp' : (p ⋙ Over.map g).IsHomLift ((Over.map g).map k) φ := isHomLift_comp_map p k φ hl
  refine { universal_property' := ?_ }
  intro a' k'' φ' hφ'
  have hw : k''.left ≫ (p.obj a).hom = (p.obj a').hom := by
    have hfac := CategoryTheory.IsHomLift.fac' (p ⋙ Over.map g)
      (k'' ≫ (Over.map g).map k) φ'
    have h1 : (p.map φ').left = k''.left ≫ k.left := by
      have h0 := congrArg Over.Hom.left hfac
      simp only [Functor.comp_map, Over.comp_left, Over.map_map_left, eqToHom_refl,
        Category.id_comp, Category.comp_id] at h0
      exact h0
    have h2 := Over.w (p.map φ')
    rwa [h1, Category.assoc, Over.w k] at h2
  have hk : (Over.map g).map (Over.mapDescend g k'' hw) = k'' :=
    Over.map_map_mapDescend g k'' hw
  have hφ'p : p.IsHomLift (Over.mapDescend g k'' hw ≫ k) φ' := by
    refine (isHomLift_overMap_iff p g (Over.mapDescend g k'' hw ≫ k) φ' rfl rfl).1 ?_
    rw [Functor.map_comp, hk]
    exact hφ'
  have := hφ'p
  obtain ⟨χ, ⟨hχ₁, hχ₂⟩, hχ₃⟩ := h.universal_property' (Over.mapDescend g k'' hw) φ'
  refine ⟨χ, ⟨?_, hχ₂⟩, fun ψ hψ => ?_⟩
  · rw [← hk]
    exact isHomLift_comp_map p (Over.mapDescend g k'' hw) χ hχ₁
  · refine hχ₃ ψ ⟨?_, hψ.2⟩
    refine (isHomLift_overMap_iff p g (Over.mapDescend g k'' hw) ψ rfl rfl).1 ?_
    rw [hk]
    exact hψ.1

/-- **Being strongly cartesian descends along a change of slice**, for a morphism of `𝒮` which
is already known to lie over the given morphism of `𝒞/V`. -/
lemma isStronglyCartesian_of_overMap {a b : 𝒮} {A B : Over V} (k : A ⟶ B) (φ : a ⟶ b)
    (hlift : p.IsHomLift k φ)
    (h : (p ⋙ Over.map g).IsStronglyCartesian ((Over.map g).map k) φ) :
    p.IsStronglyCartesian k φ := by
  have hl := hlift
  have hA : p.obj a = A := CategoryTheory.IsHomLift.domain_eq p k φ
  refine { universal_property' := ?_ }
  intro a' k' φ' hφ'
  have hpush : (p ⋙ Over.map g).IsHomLift ((Over.map g).map k' ≫ (Over.map g).map k) φ' := by
    rw [← Functor.map_comp]
    exact isHomLift_comp_map p (k' ≫ k) φ' hφ'
  have := hpush
  obtain ⟨χ, ⟨hχ₁, hχ₂⟩, hχ₃⟩ := h.universal_property' ((Over.map g).map k') φ'
  refine ⟨χ, ⟨(isHomLift_overMap_iff p g k' χ rfl hA).1 hχ₁, hχ₂⟩, fun ψ hψ => ?_⟩
  exact hχ₃ ψ ⟨isHomLift_comp_map p k' ψ hψ.1, hψ.2⟩

/-- **Being strongly cartesian is unchanged by a change of slice**, for a morphism of `𝒮`
already known to lie over the given morphism of `𝒞/V`. -/
lemma isStronglyCartesian_overMap_iff {a b : 𝒮} {A B : Over V} (k : A ⟶ B) (φ : a ⟶ b)
    (hlift : p.IsHomLift k φ) :
    (p ⋙ Over.map g).IsStronglyCartesian ((Over.map g).map k) φ ↔
      p.IsStronglyCartesian k φ :=
  ⟨isStronglyCartesian_of_overMap p g k φ hlift, isStronglyCartesian_overMap p g k φ⟩

/-- **A restriction read after a change of slice.** The restricting object and the cartesian
morphism are unchanged; only the two conditions on them are transported. -/
def Restriction.overMap {A B : Over V} {f : A ⟶ B} {x : 𝒮} {hx : p.obj x = B}
    (xr : Restriction p f x hx) :
    Restriction (p ⋙ Over.map g) ((Over.map g).map f) x
      (congrArg (Over.map g).obj hx) where
  pt := xr.pt
  hpt := congrArg (Over.map g).obj xr.hpt
  hom := xr.hom
  isHomLift := by
    have h := isHomLift_comp_map (g := g) p (eqToHom xr.hpt ≫ f ≫ eqToHom hx.symm) xr.hom
      xr.isHomLift
    simpa only [Functor.map_comp, eqToHom_map] using h
  isCart := by
    have h := isStronglyCartesian_overMap p g (eqToHom xr.hpt ≫ f ≫ eqToHom hx.symm) xr.hom
      xr.isCart
    simpa only [Functor.map_comp, eqToHom_map] using h

/-- Reading a restriction after a change of slice keeps its restricting object. -/
@[simp]
lemma Restriction.overMap_pt {A B : Over V} {f : A ⟶ B} {x : 𝒮} {hx : p.obj x = B}
    (xr : Restriction p f x hx) : (xr.overMap p g).pt = xr.pt :=
  rfl

/-- Reading a restriction after a change of slice keeps its cartesian morphism. -/
@[simp]
lemma Restriction.overMap_hom {A B : Over V} {f : A ⟶ B} {x : 𝒮} {hx : p.obj x = B}
    (xr : Restriction p f x hx) : (xr.overMap p g).hom = xr.hom :=
  rfl

/-- The object of `𝒞/V` that the source of a restriction for the changed slice along
`(Over.map g).map f` lies over is the source `A` of `f`. -/
lemma Restriction.obj_eq_of_overMap {A B : Over V} (f : A ⟶ B) {x : 𝒮} (hx : p.obj x = B)
    (xr : Restriction (p ⋙ Over.map g) ((Over.map g).map f) x
      (congrArg (Over.map g).obj hx)) :
    p.obj xr.pt = A := by
  refine (obj_eq_of_isHomLift_comp_map (g := g) p (f ≫ eqToHom hx.symm) xr.hom ?_).symm
  refine CategoryTheory.IsHomLift.of_fac' (p ⋙ Over.map g) _ xr.hom xr.hpt rfl ?_
  have h := CategoryTheory.IsHomLift.fac' (p ⋙ Over.map g)
    (eqToHom xr.hpt ≫ (Over.map g).map f ≫ eqToHom (congrArg (Over.map g).obj hx).symm)
    xr.hom
  simpa only [Functor.map_comp, eqToHom_map, eqToHom_refl, Category.comp_id,
    Category.id_comp, Category.assoc] using h

/-- The morphism of `𝒮` underlying a restriction for the changed slice lies over the
corresponding morphism of `𝒞/V`. -/
lemma Restriction.isHomLift_of_overMap {A B : Over V} (f : A ⟶ B) {x : 𝒮} (hx : p.obj x = B)
    (xr : Restriction (p ⋙ Over.map g) ((Over.map g).map f) x
      (congrArg (Over.map g).obj hx)) :
    p.IsHomLift (eqToHom (Restriction.obj_eq_of_overMap p g f hx xr) ≫ f ≫ eqToHom hx.symm)
      xr.hom := by
  refine (isHomLift_overMap_iff p g _ xr.hom rfl rfl).1 ?_
  simpa only [Functor.map_comp, eqToHom_map] using xr.isHomLift

/-- **A restriction for the changed slice descends.** The restricting object and the cartesian
morphism are again unchanged; the object of `𝒞/V` it is a restriction to is
`CategoryTheory.Functor.Restriction.obj_eq_of_overMap`. -/
def Restriction.ofOverMap {A B : Over V} (f : A ⟶ B) {x : 𝒮} (hx : p.obj x = B)
    (xr : Restriction (p ⋙ Over.map g) ((Over.map g).map f) x
      (congrArg (Over.map g).obj hx)) :
    Restriction p f x hx where
  pt := xr.pt
  hpt := Restriction.obj_eq_of_overMap p g f hx xr
  hom := xr.hom
  isHomLift := Restriction.isHomLift_of_overMap p g f hx xr
  isCart := by
    refine (isStronglyCartesian_overMap_iff p g _ xr.hom
      (Restriction.isHomLift_of_overMap p g f hx xr)).1 ?_
    simpa only [Functor.map_comp, eqToHom_map] using xr.isCart

/-- Descending a restriction for the changed slice keeps its restricting object. -/
@[simp]
lemma Restriction.ofOverMap_pt {A B : Over V} (f : A ⟶ B) {x : 𝒮} (hx : p.obj x = B)
    (xr : Restriction (p ⋙ Over.map g) ((Over.map g).map f) x
      (congrArg (Over.map g).obj hx)) :
    (Restriction.ofOverMap p g f hx xr).pt = xr.pt :=
  rfl

/-- Descending a restriction for the changed slice keeps its cartesian morphism. -/
@[simp]
lemma Restriction.ofOverMap_hom {A B : Over V} (f : A ⟶ B) {x : 𝒮} (hx : p.obj x = B)
    (xr : Restriction (p ⋙ Over.map g) ((Over.map g).map f) x
      (congrArg (Over.map g).obj hx)) :
    (Restriction.ofOverMap p g f hx xr).hom = xr.hom :=
  rfl

/-- **The canonical comparison of two restrictions is unchanged by a change of slice.** -/
lemma compTo_overMap {A B D : Over V} (k : A ⟶ B) (f : B ⟶ D) {h : A ⟶ D} (hh : h = k ≫ f)
    {x : 𝒮} {hx : p.obj x = D} (xr : Restriction p f x hx) (xrA : Restriction p h x hx) :
    Restriction.compTo (p ⋙ Over.map g) ((Over.map g).map k) ((Over.map g).map f)
        (by rw [hh, Functor.map_comp]) (xr.overMap p g) (xrA.overMap p g) =
      Restriction.compTo p k f hh xr xrA := by
  have hH : p.IsHomLift k (Restriction.compTo p k f hh xr xrA) := by
    have hcart := xr.isCart
    have hlift : p.IsHomLift ((eqToHom xrA.hpt ≫ k ≫ eqToHom xr.hpt.symm) ≫
        (eqToHom xr.hpt ≫ f ≫ eqToHom hx.symm)) xrA.hom := by
      have hl0 := xrA.isHomLift
      have e : (eqToHom xrA.hpt ≫ k ≫ eqToHom xr.hpt.symm) ≫
          (eqToHom xr.hpt ≫ f ≫ eqToHom hx.symm)
          = eqToHom xrA.hpt ≫ h ≫ eqToHom hx.symm := by subst hh; simp
      rwa [e]
    have := hlift
    have h0 : p.IsHomLift (eqToHom xrA.hpt ≫ k ≫ eqToHom xr.hpt.symm)
        (Restriction.compTo p k f hh xr xrA) :=
      IsStronglyCartesian.map_isHomLift p (eqToHom xr.hpt ≫ f ≫ eqToHom hx.symm) xr.hom
        rfl xrA.hom
    have := h0
    refine CategoryTheory.IsHomLift.of_fac' p k _ xrA.hpt xr.hpt ?_
    simpa using CategoryTheory.IsHomLift.fac' p (eqToHom xrA.hpt ≫ k ≫ eqToHom xr.hpt.symm)
      (Restriction.compTo p k f hh xr xrA)
  refine (Restriction.eq_compTo ((Over.map g).map k) ((Over.map g).map f)
    (by rw [hh, Functor.map_comp]) (xr.overMap p g) (xrA.overMap p g)
    (Restriction.compTo p k f hh xr xrA) ?_ ?_).symm
  · exact (isHomLift_overMap_iff p g k _ xrA.hpt xr.hpt).2 hH
  · exact Restriction.compTo_hom p k f hh xr xrA

/-- **The fibre-morphism condition is unchanged by a change of slice.** -/
lemma fibreHom_overMap_iff {U : Over V} (a b : 𝒮) (ha : p.obj a = U) (hb : p.obj b = U)
    (φ : a ⟶ b) :
    FibreHom (p ⋙ Over.map g) a b (congrArg (Over.map g).obj ha)
        (congrArg (Over.map g).obj hb) φ ↔ FibreHom p a b ha hb φ := by
  have hm : (Over.map g).map (eqToHom ha ≫ eqToHom hb.symm)
      = eqToHom (congrArg (Over.map g).obj ha) ≫
        eqToHom (congrArg (Over.map g).obj hb).symm := by
    simp only [Functor.map_comp, eqToHom_map]
  rw [show FibreHom p a b ha hb φ = p.IsHomLift (eqToHom ha ≫ eqToHom hb.symm) φ from rfl,
    ← isHomLift_overMap_iff p g (eqToHom ha ≫ eqToHom hb.symm) φ rfl rfl, hm]

/-- The fibre-morphism condition for the changed slice is the one for `p`, whichever objects of the
two slices the two objects are recorded as lying over. -/
private lemma fibreHom_comp_overMap_iff {U : Over V} {U' : Over W} (a b : 𝒮)
    (ha : p.obj a = U) (hb : p.obj b = U) (ha' : (p ⋙ Over.map g).obj a = U')
    (hb' : (p ⋙ Over.map g).obj b = U') (φ : a ⟶ b) :
    FibreHom (p ⋙ Over.map g) a b ha' hb' φ ↔ FibreHom p a b ha hb φ :=
  (fibreHom_congr _ _ _ _ _ _).trans (fibreHom_overMap_iff p g a b ha hb φ)

/-- **The canonical-restriction relation is unchanged by a change of slice.** -/
lemma isRestrictionOf_overMap_iff {A Bx By D : Over V} (k : A ⟶ D) (fx : D ⟶ Bx) (fy : D ⟶ By)
    {hx_ : A ⟶ Bx} {hy_ : A ⟶ By} (hfx : hx_ = k ≫ fx) (hfy : hy_ = k ≫ fy)
    {x y : 𝒮} {hx : p.obj x = Bx} {hy : p.obj y = By}
    (xr : Restriction p fx x hx) (yr : Restriction p fy y hy)
    (xrA : Restriction p hx_ x hx) (yrA : Restriction p hy_ y hy)
    (α : xr.pt ⟶ yr.pt) (β : xrA.pt ⟶ yrA.pt) :
    IsRestrictionOf (p ⋙ Over.map g) ((Over.map g).map k)
        (by rw [hfx, Functor.map_comp]) (by rw [hfy, Functor.map_comp])
        (xr.overMap p g) (yr.overMap p g) (xrA.overMap p g) (yrA.overMap p g) α β ↔
      IsRestrictionOf p k hfx hfy xr yr xrA yrA α β := by
  rw [show IsRestrictionOf p k hfx hfy xr yr xrA yrA α β =
      (β ≫ Restriction.compTo p k fy hfy yr yrA =
        Restriction.compTo p k fx hfx xr xrA ≫ α) from rfl,
    ← compTo_overMap p g k fy hfy yr yrA, ← compTo_overMap p g k fx hfx xr xrA]
  rfl


/-- **The forward half of the stack-in-groupoids clause across a change of slice.** For a
subcanonical topology, if `𝒮`, viewed over the slice at `W` along `g : V ⟶ W`, is a stack in
groupoids for the localized topology there, then it is a stack in groupoids over the slice at
`V`. -/
theorem isStackInGroupoids_of_comp_overMap (J : GrothendieckTopology C) [J.Subcanonical]
    (h : (p ⋙ Over.map g).IsStackInGroupoids.{w} (J.over W)) :
    p.IsStackInGroupoids.{w} (J.over V) where
  isFiberedInGroupoids :=
    (isFiberedInGroupoids_comp_overMap_iff g p).1 h.isFiberedInGroupoids
  isom_isSheaf := by
    intro U x y hx hy I Z f hcov Zij pr₁ pr₂ hZij xr yr xrij yrij φ hφfib hφiso hφγ
    obtain ⟨G, ⟨hG₁, hG₂, hG₃⟩, hGu⟩ := h.isom_isSheaf x y
      (congrArg (Over.map g).obj hx) (congrArg (Over.map g).obj hy)
      (fun i => (Over.map g).obj (Z i)) (fun i => (Over.map g).map (f i))
      ((Over.mem_over_map_iff J g Z f).2 hcov)
      (fun i j => (Over.map g).obj (Zij i j))
      (fun i j => (Over.map g).map (pr₁ i j)) (fun i j => (Over.map g).map (pr₂ i j))
      (fun i j => (Over.isPullback_map_iff g _ _ _ _ (hZij i j).w).2 (hZij i j))
      (fun i => (xr i).overMap p g) (fun i => (yr i).overMap p g)
      (fun i j => (xrij i j).overMap p g) (fun i j => (yrij i j).overMap p g)
      φ
      (fun i => (fibreHom_overMap_iff p g _ _ (xr i).hpt (yr i).hpt (φ i)).2 (hφfib i))
      hφiso
      (by
        intro i j
        obtain ⟨γ, hγfib, hγ₁, hγ₂⟩ := hφγ i j
        refine ⟨γ, (fibreHom_overMap_iff p g _ _ (xrij i j).hpt (yrij i j).hpt γ).2 hγfib,
          ?_, ?_⟩
        · exact (isRestrictionOf_overMap_iff p g (pr₁ i j) (f i) (f i) rfl rfl
            (xr i) (yr i) (xrij i j) (yrij i j) (φ i) γ).2 hγ₁
        · exact (isRestrictionOf_overMap_iff p g (pr₂ i j) (f j) (f j)
            (hZij i j).w (hZij i j).w (xr j) (yr j) (xrij i j) (yrij i j) (φ j) γ).2 hγ₂)
    refine ⟨G, ⟨(fibreHom_overMap_iff p g x y hx hy G).1 hG₁, hG₂, hG₃⟩, fun G' hG' => ?_⟩
    exact hGu G' ⟨(fibreHom_overMap_iff p g x y hx hy G').2 hG'.1, hG'.2.1, hG'.2.2⟩
  effective_descent := by
    intro U I Z f hcov Zij pr₁ pr₂ hZij Zijk s₁₂ s₂₃ hZijk q₁ q₂ q₃ hq₁ hq₂ hq₃ D
    have hcov' := (Over.mem_over_map_iff J g Z f).2 hcov
    obtain ⟨xx, hxx, xr, ψ, hψfib, hψiso, hψov⟩ := h.effective_descent
      (fun i => (Over.map g).obj (Z i)) (fun i => (Over.map g).map (f i)) hcov'
      (fun i j => (Over.map g).obj (Zij i j))
      (fun i j => (Over.map g).map (pr₁ i j)) (fun i j => (Over.map g).map (pr₂ i j))
      (fun i j => (Over.isPullback_map_iff g _ _ _ _ (hZij i j).w).2 (hZij i j))
      (fun i j k => (Over.map g).obj (Zijk i j k))
      (fun i j k => (Over.map g).map (s₁₂ i j k)) (fun i j k => (Over.map g).map (s₂₃ i j k))
      (fun i j k => (Over.isPullback_map_iff g _ _ _ _ (hZijk i j k).w).2 (hZijk i j k))
      (fun i j k => (Over.map g).map (q₁ i j k)) (fun i j k => (Over.map g).map (q₂ i j k))
      (fun i j k => (Over.map g).map (q₃ i j k))
      (fun i j k => congrArg (Over.map g).map (hq₁ i j k))
      (fun i j k => congrArg (Over.map g).map (hq₂ i j k))
      (fun i j k => congrArg (Over.map g).map (hq₃ i j k))
      { x := D.x
        hx := fun i => congrArg (Over.map g).obj (D.hx i)
        xrij := fun i j => (D.xrij i j).overMap p g
        xrji := fun i j => (D.xrji i j).overMap p g
        φ := D.φ
        φ_fibreHom := fun i j => (fibreHom_overMap_iff p g _ _ (D.xrij i j).hpt
          (D.xrji i j).hpt (D.φ i j)).2 (D.φ_fibreHom i j)
        φ_iso := D.φ_iso
        wi := fun i j k => (D.wi i j k).overMap p g
        wj := fun i j k => (D.wj i j k).overMap p g
        wk := fun i j k => (D.wk i j k).overMap p g
        αij := D.αij
        αjk := D.αjk
        αik := D.αik
        αij_restr := fun i j k => (isRestrictionOf_overMap_iff p g (s₁₂ i j k) (pr₁ i j)
          (pr₂ i j) (hq₁ i j k) (hq₂ i j k) (D.xrij i j) (D.xrji i j) (D.wi i j k)
          (D.wj i j k) (D.φ i j) (D.αij i j k)).2 (D.αij_restr i j k)
        αjk_restr := fun i j k => (isRestrictionOf_overMap_iff p g (s₂₃ i j k) (pr₁ j k)
          (pr₂ j k) ((hq₂ i j k).trans (hZijk i j k).w) (hq₃ i j k) (D.xrij j k) (D.xrji j k)
          (D.wj i j k) (D.wk i j k) (D.φ j k) (D.αjk i j k)).2 (D.αjk_restr i j k)
        s₁₃ := fun i j k => (Over.map g).map (D.s₁₃ i j k)
        hs₁₃₁ := fun i j k => by
          rw [← Functor.map_comp, D.hs₁₃₁ i j k]
        hs₁₃₂ := fun i j k => by
          rw [← Functor.map_comp, D.hs₁₃₂ i j k]
        αik_restr := fun i j k => (isRestrictionOf_overMap_iff p g (D.s₁₃ i j k) (pr₁ i k)
          (pr₂ i k) (D.hs₁₃₁ i j k).symm (D.hs₁₃₂ i j k).symm (D.xrij i k) (D.xrji i k)
          (D.wi i j k) (D.wk i j k) (D.φ i k) (D.αik i j k)).2 (D.αik_restr i j k)
        cocycle := D.cocycle }
    have hleft : U.left = (p.obj xx).left := (congrArg CostructuredArrow.left hxx).symm
    have hZ : ∀ i, Z i = p.obj (xr i).pt := by
      intro i
      refine obj_eq_of_isHomLift_comp_map (g := g) p (eqToHom (D.hx i).symm) (ψ i) ?_
      refine CategoryTheory.IsHomLift.of_fac' (p ⋙ Over.map g) _ (ψ i) (xr i).hpt rfl ?_
      have h0 := CategoryTheory.IsHomLift.fac' (p ⋙ Over.map g)
        (eqToHom (xr i).hpt ≫ eqToHom (congrArg (Over.map g).obj (D.hx i)).symm) (ψ i)
      simpa only [eqToHom_map, eqToHom_refl, Category.comp_id, Category.id_comp,
        Category.assoc] using h0
    have hstr : ∀ i, (f i).left ≫ eqToHom hleft ≫ (p.obj xx).hom = (f i).left ≫ U.hom := by
      intro i
      have hw := Over.w (p.map (xr i).hom)
      have hl : (p.map (xr i).hom).left
          = eqToHom (congrArg CostructuredArrow.left (hZ i).symm) ≫ (f i).left
            ≫ eqToHom hleft := by
        have h0 := congrArg Over.Hom.left (CategoryTheory.IsHomLift.fac'
          (p ⋙ Over.map g) (eqToHom (xr i).hpt ≫ (Over.map g).map (f i) ≫
            eqToHom hxx.symm) (xr i).hom)
        simp only [Functor.comp_map, Over.comp_left, Over.eqToHom_left, Over.map_map_left,
          Category.assoc] at h0
        rw [h0]
        simp
      rw [hl, Category.assoc, Category.assoc] at hw
      have he : eqToHom (congrArg CostructuredArrow.left (hZ i)) ≫
          (p.obj (xr i).pt).hom = (Z i).hom := by
        have h1 := Over.w (eqToHom (hZ i) : Z i ⟶ p.obj (xr i).pt)
        simpa [Over.eqToHom_left] using h1
      rw [Over.w (f i), ← he, ← hw]
      simp
    have key : eqToHom hleft ≫ (p.obj xx).hom = U.hom :=
      Over.eq_of_mem_over J Z f hcov _ U.hom hstr
    obtain rfl : p.obj xx = U := by
      refine CostructuredArrow.obj_ext _ _ hleft.symm ?_
      show eqToHom hleft.symm ≫ U.hom = (p.obj xx).hom
      rw [← key]
      simp
    refine ⟨xx, rfl, fun i => Restriction.ofOverMap p g (f i) rfl (xr i), ψ, ?_, hψiso, ?_⟩
    · exact fun i => (fibreHom_overMap_iff p g _ _ (Restriction.obj_eq_of_overMap p g (f i) rfl
        (xr i)) (D.hx i) (ψ i)).1 (hψfib i)
    · intro i j
      obtain ⟨xrij, ψir, ψjr, hψir, hψjr, hir, hjr, hr₁, hr₂, hcomp⟩ := hψov i j
      refine ⟨Restriction.ofOverMap p g (pr₁ i j ≫ f i) rfl xrij, ψir, ψjr, ?_, ?_, hir, hjr,
        ?_, ?_, hcomp⟩
      · exact (fibreHom_overMap_iff p g _ _ (Restriction.obj_eq_of_overMap p g
          (pr₁ i j ≫ f i) rfl xrij) (D.xrij i j).hpt ψir).1 hψir
      · exact (fibreHom_overMap_iff p g _ _ (Restriction.obj_eq_of_overMap p g
          (pr₁ i j ≫ f i) rfl xrij) (D.xrji i j).hpt ψjr).1 hψjr
      · exact (isRestrictionOf_overMap_iff p g (pr₁ i j) (f i) (𝟙 (Z i)) rfl (by simp)
          (Restriction.ofOverMap p g (f i) rfl (xr i)) (Restriction.id p (D.x i) (D.hx i))
          (Restriction.ofOverMap p g (pr₁ i j ≫ f i) rfl xrij) (D.xrij i j) (ψ i) ψir).1 hr₁
      · exact (isRestrictionOf_overMap_iff p g (pr₂ i j) (f j) (𝟙 (Z j)) (hZij i j).w (by simp)
          (Restriction.ofOverMap p g (f j) rfl (xr j)) (Restriction.id p (D.x j) (D.hx j))
          (Restriction.ofOverMap p g (pr₁ i j ≫ f i) rfl xrij) (D.xrji i j) (ψ j) ψjr).1 hr₂

/-! ### The converse of the stack-in-groupoids implication -/

/-- **Two objects of `𝒞/V` carrying objects of `𝒮` joined by a morphism of the fibre are equal.**
If two objects of `𝒮` lying over the same object of `𝒞/W` for the changed slice are joined by a
morphism of that fibre, then they lie over the same object of `𝒞/V`. -/
lemma obj_eq_of_fibreHom_overMap {U' : Over W} {a b : 𝒮}
    (ha : (p ⋙ Over.map g).obj a = U') (hb : (p ⋙ Over.map g).obj b = U') (φ : a ⟶ b)
    (hφ : FibreHom (p ⋙ Over.map g) a b ha hb φ) : p.obj a = p.obj b := by
  have := hφ
  have hl := congrArg CostructuredArrow.left (ha.trans hb.symm)
  have hleft : (p.obj a).left = (p.obj b).left := hl
  refine Over.eq_of_hom_left_eq_eqToHom (p.map φ) hleft ?_
  have h0 := CategoryTheory.IsHomLift.eq_of_isHomLift (p ⋙ Over.map g)
    (eqToHom ha ≫ eqToHom hb.symm) φ
  have h1 := congrArg Over.Hom.left h0
  simp only [Over.eqToHom_left, Functor.comp_map, Over.map_map_left, eqToHom_trans] at h1
  simpa using h1.symm

/-- **A restriction for the changed slice descends, along a given base morphism of `𝒞/V`.** The
restricting object and the cartesian morphism are unchanged; the two objects of `𝒞/V` involved and
the morphism between them are given, together with the identification of the image of that
morphism with the base morphism of `𝒞/W`. -/
@[implicit_reducible]
def Restriction.descend {Z U' : Over W} {f : Z ⟶ U'} {x : 𝒮}
    {hx : (p ⋙ Over.map g).obj x = U'} (xr : Restriction (p ⋙ Over.map g) f x hx)
    {A B : Over V} {f₀ : A ⟶ B} (hA : p.obj xr.pt = A) (hB : p.obj x = B)
    (hf : (Over.map g).map (eqToHom hA ≫ f₀ ≫ eqToHom hB.symm)
      = eqToHom xr.hpt ≫ f ≫ eqToHom hx.symm) :
    Restriction p f₀ x hB where
  pt := xr.pt
  hpt := hA
  hom := xr.hom
  isHomLift := by
    refine (isHomLift_overMap_iff p g _ xr.hom rfl rfl).1 ?_
    rw [hf]; exact xr.isHomLift
  isCart := by
    refine isStronglyCartesian_of_overMap p g _ xr.hom ?_ ?_
    · refine (isHomLift_overMap_iff p g _ xr.hom rfl rfl).1 ?_
      rw [hf]; exact xr.isHomLift
    · rw [hf]; exact xr.isCart

/-- `CategoryTheory.Functor.Restriction.descend` keeps the restricting object. -/
@[simp]
lemma Restriction.descend_pt {Z U' : Over W} {f : Z ⟶ U'} {x : 𝒮}
    {hx : (p ⋙ Over.map g).obj x = U'} (xr : Restriction (p ⋙ Over.map g) f x hx)
    {A B : Over V} {f₀ : A ⟶ B} (hA : p.obj xr.pt = A) (hB : p.obj x = B)
    (hf : (Over.map g).map (eqToHom hA ≫ f₀ ≫ eqToHom hB.symm)
      = eqToHom xr.hpt ≫ f ≫ eqToHom hx.symm) :
    (xr.descend p g hA hB hf).pt = xr.pt :=
  rfl

/-- `CategoryTheory.Functor.Restriction.descend` keeps the cartesian morphism. -/
@[simp]
lemma Restriction.descend_hom {Z U' : Over W} {f : Z ⟶ U'} {x : 𝒮}
    {hx : (p ⋙ Over.map g).obj x = U'} (xr : Restriction (p ⋙ Over.map g) f x hx)
    {A B : Over V} {f₀ : A ⟶ B} (hA : p.obj xr.pt = A) (hB : p.obj x = B)
    (hf : (Over.map g).map (eqToHom hA ≫ f₀ ≫ eqToHom hB.symm)
      = eqToHom xr.hpt ≫ f ≫ eqToHom hx.symm) :
    (xr.descend p g hA hB hf).hom = xr.hom :=
  rfl

/-- **The object of `𝒞/V` that the source of a restriction for the changed slice lies over.** For
a factorization `c` of the structure morphism of the target through `g`, it is
`Over.mk (f.left ≫ c)`. -/
lemma Restriction.obj_pt_eq {U' : Over W} {c : U'.left ⟶ V} {x : 𝒮}
    (hc : p.obj x = Over.mk c) {Z : Over W} {f : Z ⟶ U'}
    {hx : (p ⋙ Over.map g).obj x = U'} (xr : Restriction (p ⋙ Over.map g) f x hx) :
    p.obj xr.pt = Over.mk (f.left ≫ c) := by
  have hwx := Over.w (eqToHom hc : p.obj x ⟶ Over.mk c)
  have hw := Over.w (p.map xr.hom)
  have h0 := CategoryTheory.IsHomLift.eq_of_isHomLift (p ⋙ Over.map g)
    (eqToHom xr.hpt ≫ f ≫ eqToHom hx.symm) xr.hom
  have h1 := congrArg Over.Hom.left h0
  simp only [Over.comp_left, Over.eqToHom_left, Functor.comp_map, Over.map_map_left] at h1
  simp only [Over.eqToHom_left] at hwx
  have hl := congrArg CostructuredArrow.left xr.hpt
  have hleft : (p.obj xr.pt).left = (Over.mk (f.left ≫ c) : Over V).left := hl
  have key : (p.obj xr.pt).hom = eqToHom hleft ≫ f.left ≫ c := by
    rw [← hw, ← h1, ← hwx]
    simp
  refine CostructuredArrow.obj_ext _ _ hleft ?_
  simpa using key.symm

/-- **The canonical comparison of two restrictions is unchanged by descending them.** -/
lemma compTo_descend [p.IsFibered]
    {Aw Dw Bw : Over W} {k : Dw ⟶ Aw} {fw : Aw ⟶ Bw} {mw : Dw ⟶ Bw} (hm : mw = k ≫ fw)
    {x : 𝒮} {hx : (p ⋙ Over.map g).obj x = Bw}
    (xr : Restriction (p ⋙ Over.map g) fw x hx) (xrA : Restriction (p ⋙ Over.map g) mw x hx)
    {A D B : Over V} {k₀ : D ⟶ A} {f₀ : A ⟶ B} {m₀ : D ⟶ B} (hm₀ : m₀ = k₀ ≫ f₀)
    (hA : p.obj xr.pt = A) (hD : p.obj xrA.pt = D) (hB : p.obj x = B)
    (hfm : (Over.map g).map (eqToHom hA ≫ f₀ ≫ eqToHom hB.symm)
      = eqToHom xr.hpt ≫ fw ≫ eqToHom hx.symm)
    (hmm : (Over.map g).map (eqToHom hD ≫ m₀ ≫ eqToHom hB.symm)
      = eqToHom xrA.hpt ≫ mw ≫ eqToHom hx.symm)
    (hk : (Over.map g).map (eqToHom hD ≫ k₀ ≫ eqToHom hA.symm)
      = eqToHom xrA.hpt ≫ k ≫ eqToHom xr.hpt.symm) :
    Restriction.compTo (p ⋙ Over.map g) k fw hm xr xrA
      = Restriction.compTo p k₀ f₀ hm₀ (xr.descend p g hA hB hfm)
        (xrA.descend p g hD hB hmm) := by
  refine (Restriction.eq_compTo k fw hm xr xrA
    (Restriction.compTo p k₀ f₀ hm₀ (xr.descend p g hA hB hfm) (xrA.descend p g hD hB hmm))
    ?_ (Restriction.compTo_hom p k₀ f₀ hm₀ _ _)).symm
  have h1 : p.IsHomLift k₀ (Restriction.compTo p k₀ f₀ hm₀ (xr.descend p g hA hB hfm)
      (xrA.descend p g hD hB hmm)) := Restriction.isHomLift_compTo k₀ f₀ hm₀ _ _
  have := h1
  refine CategoryTheory.IsHomLift.of_fac' (p ⋙ Over.map g) k _ xrA.hpt xr.hpt ?_
  have h2 := CategoryTheory.IsHomLift.fac' p k₀
    (Restriction.compTo p k₀ f₀ hm₀ (xr.descend p g hA hB hfm) (xrA.descend p g hD hB hmm))
  have h3 : p.map (Restriction.compTo p k₀ f₀ hm₀ (xr.descend p g hA hB hfm)
      (xrA.descend p g hD hB hmm)) = eqToHom hD ≫ k₀ ≫ eqToHom hA.symm := h2
  show (Over.map g).map (p.map _) = _
  rw [h3, hk]

/-- **The canonical-restriction relation is unchanged by descending the four restrictions.** -/
lemma isRestrictionOf_descend_iff [p.IsFibered]
    {Aw Bxw Byw Dw : Over W} {k : Dw ⟶ Aw} {fx : Aw ⟶ Bxw} {fy : Aw ⟶ Byw}
    {mx : Dw ⟶ Bxw} {my : Dw ⟶ Byw} (hfx : mx = k ≫ fx) (hfy : my = k ≫ fy)
    {x y : 𝒮} {hx : (p ⋙ Over.map g).obj x = Bxw} {hy : (p ⋙ Over.map g).obj y = Byw}
    (xr : Restriction (p ⋙ Over.map g) fx x hx) (yr : Restriction (p ⋙ Over.map g) fy y hy)
    (xrA : Restriction (p ⋙ Over.map g) mx x hx) (yrA : Restriction (p ⋙ Over.map g) my y hy)
    {A Bx By D : Over V} {k₀ : D ⟶ A} {fx₀ : A ⟶ Bx} {fy₀ : A ⟶ By}
    {mx₀ : D ⟶ Bx} {my₀ : D ⟶ By} (hfx₀ : mx₀ = k₀ ≫ fx₀) (hfy₀ : my₀ = k₀ ≫ fy₀)
    (hxA : p.obj xr.pt = A) (hyA : p.obj yr.pt = A)
    (hxD : p.obj xrA.pt = D) (hyD : p.obj yrA.pt = D)
    (hxB : p.obj x = Bx) (hyB : p.obj y = By)
    (hfxm : (Over.map g).map (eqToHom hxA ≫ fx₀ ≫ eqToHom hxB.symm)
      = eqToHom xr.hpt ≫ fx ≫ eqToHom hx.symm)
    (hfym : (Over.map g).map (eqToHom hyA ≫ fy₀ ≫ eqToHom hyB.symm)
      = eqToHom yr.hpt ≫ fy ≫ eqToHom hy.symm)
    (hmxm : (Over.map g).map (eqToHom hxD ≫ mx₀ ≫ eqToHom hxB.symm)
      = eqToHom xrA.hpt ≫ mx ≫ eqToHom hx.symm)
    (hmym : (Over.map g).map (eqToHom hyD ≫ my₀ ≫ eqToHom hyB.symm)
      = eqToHom yrA.hpt ≫ my ≫ eqToHom hy.symm)
    (hkx : (Over.map g).map (eqToHom hxD ≫ k₀ ≫ eqToHom hxA.symm)
      = eqToHom xrA.hpt ≫ k ≫ eqToHom xr.hpt.symm)
    (hky : (Over.map g).map (eqToHom hyD ≫ k₀ ≫ eqToHom hyA.symm)
      = eqToHom yrA.hpt ≫ k ≫ eqToHom yr.hpt.symm)
    (α : xr.pt ⟶ yr.pt) (β : xrA.pt ⟶ yrA.pt) :
    IsRestrictionOf (p ⋙ Over.map g) k hfx hfy xr yr xrA yrA α β ↔
      IsRestrictionOf p k₀ hfx₀ hfy₀ (xr.descend p g hxA hxB hfxm) (yr.descend p g hyA hyB hfym)
        (xrA.descend p g hxD hxB hmxm) (yrA.descend p g hyD hyB hmym) α β := by
  rw [show IsRestrictionOf (p ⋙ Over.map g) k hfx hfy xr yr xrA yrA α β =
      (β ≫ Restriction.compTo (p ⋙ Over.map g) k fy hfy yr yrA =
        Restriction.compTo (p ⋙ Over.map g) k fx hfx xr xrA ≫ α) from rfl,
    compTo_descend p g hfy yr yrA hfy₀ hyA hyD hyB hfym hmym hky,
    compTo_descend p g hfx xr xrA hfx₀ hxA hxD hxB hfxm hmxm hkx]

/-- **A restriction read for the changed slice, along a given base morphism of `𝒞/W`.** The
restriction `CategoryTheory.Functor.Restriction.overMap`, read along a base morphism of `𝒞/W`
equal to the image of `f₀` by `CategoryTheory.Functor.Restriction.ofEq`. -/
@[implicit_reducible]
def Restriction.toOverMap {A B : Over V} {f₀ : A ⟶ B} {x : 𝒮} {hB : p.obj x = B}
    (xr : Restriction p f₀ x hB) {Z U' : Over W} {f : Z ⟶ U'}
    (eA : (Over.map g).obj A = Z) (eB : (Over.map g).obj B = U')
    (hf : f = eqToHom eA.symm ≫ (Over.map g).map f₀ ≫ eqToHom eB)
    (hx : (p ⋙ Over.map g).obj x = U') :
    Restriction (p ⋙ Over.map g) f x hx :=
  (xr.overMap p g).ofEq (p ⋙ Over.map g) eA eB hf hx

/-- `CategoryTheory.Functor.Restriction.toOverMap` keeps the restricting object. -/
@[simp]
lemma Restriction.toOverMap_pt {A B : Over V} {f₀ : A ⟶ B} {x : 𝒮} {hB : p.obj x = B}
    (xr : Restriction p f₀ x hB) {Z U' : Over W} {f : Z ⟶ U'}
    (eA : (Over.map g).obj A = Z) (eB : (Over.map g).obj B = U')
    (hf : f = eqToHom eA.symm ≫ (Over.map g).map f₀ ≫ eqToHom eB)
    (hx : (p ⋙ Over.map g).obj x = U') :
    (xr.toOverMap p g eA eB hf hx).pt = xr.pt :=
  rfl

/-- **The canonical-restriction relation is unchanged by reading the four restrictions for the
changed slice.** -/
lemma isRestrictionOf_toOverMap_iff [p.IsFibered] [(p ⋙ Over.map g).IsFibered]
    {A Bx By Dv : Over V} {k₀ : Dv ⟶ A} {fx₀ : A ⟶ Bx} {fy₀ : A ⟶ By}
    {mx₀ : Dv ⟶ Bx} {my₀ : Dv ⟶ By} (hfx₀ : mx₀ = k₀ ≫ fx₀) (hfy₀ : my₀ = k₀ ≫ fy₀)
    {x y : 𝒮} {hxB : p.obj x = Bx} {hyB : p.obj y = By}
    (xr : Restriction p fx₀ x hxB) (yr : Restriction p fy₀ y hyB)
    (xrA : Restriction p mx₀ x hxB) (yrA : Restriction p my₀ y hyB)
    {Aw Bxw Byw Dw : Over W} {k : Dw ⟶ Aw} {fx : Aw ⟶ Bxw} {fy : Aw ⟶ Byw}
    {mx : Dw ⟶ Bxw} {my : Dw ⟶ Byw} (hfxW : mx = k ≫ fx) (hfyW : my = k ≫ fy)
    (eA : (Over.map g).obj A = Aw) (eD : (Over.map g).obj Dv = Dw)
    (eBx : (Over.map g).obj Bx = Bxw) (eBy : (Over.map g).obj By = Byw)
    (hke : k = eqToHom eD.symm ≫ (Over.map g).map k₀ ≫ eqToHom eA)
    (hfxe : fx = eqToHom eA.symm ≫ (Over.map g).map fx₀ ≫ eqToHom eBx)
    (hfye : fy = eqToHom eA.symm ≫ (Over.map g).map fy₀ ≫ eqToHom eBy)
    (hmxe : mx = eqToHom eD.symm ≫ (Over.map g).map mx₀ ≫ eqToHom eBx)
    (hmye : my = eqToHom eD.symm ≫ (Over.map g).map my₀ ≫ eqToHom eBy)
    (hx : (p ⋙ Over.map g).obj x = Bxw) (hy : (p ⋙ Over.map g).obj y = Byw)
    (α : xr.pt ⟶ yr.pt) (β : xrA.pt ⟶ yrA.pt) :
    IsRestrictionOf (p ⋙ Over.map g) k hfxW hfyW
        (xr.toOverMap p g eA eBx hfxe hx) (yr.toOverMap p g eA eBy hfye hy)
        (xrA.toOverMap p g eD eBx hmxe hx) (yrA.toOverMap p g eD eBy hmye hy) α β ↔
      IsRestrictionOf p k₀ hfx₀ hfy₀ xr yr xrA yrA α β :=
  Iff.trans
    (isRestrictionOf_ofEq (p ⋙ Over.map g) eD eA eBx eBy
      (by rw [hfx₀, Functor.map_comp]) (by rw [hfy₀, Functor.map_comp]) hfxW hfyW
      hke hfxe hfye hmxe hmye hx hy (xr.overMap p g) (yr.overMap p g)
      (xrA.overMap p g) (yrA.overMap p g) α β)
    (isRestrictionOf_overMap_iff p g k₀ fx₀ fy₀ hfx₀ hfy₀ xr yr xrA yrA α β)

/-- **An object of `𝒮` lying over an object of `𝒞/W` for the changed slice lies over a
factorization of its structure morphism through `g`.** The factorization is the structure
morphism of the object of `𝒞/V` that it lies over, read through the identification of underlying
objects. -/
lemma obj_eq_mk_of_overMap {U' : Over W} {x : 𝒮} (hx : (p ⋙ Over.map g).obj x = U') :
    p.obj x = Over.mk (eqToHom (congrArg CostructuredArrow.left hx).symm ≫ (p.obj x).hom) := by
  have hl := congrArg CostructuredArrow.left hx
  have hleft : (p.obj x).left = U'.left := hl
  refine CostructuredArrow.obj_ext _ _ hleft ?_
  simp

/-- **The converse half of the stack-in-groupoids clause across a change of slice.** For a
subcanonical topology, if `𝒮` is a stack in groupoids over the slice at `V` for the localized
topology there, then, viewed over the slice at `W` along `g : V ⟶ W`, it is a stack in groupoids
over the slice at `W`. -/
theorem isStackInGroupoids_comp_overMap (J : GrothendieckTopology C) [J.Subcanonical]
    (h : p.IsStackInGroupoids.{w} (J.over V)) :
    (p ⋙ Over.map g).IsStackInGroupoids.{w} (J.over W) where
  isFiberedInGroupoids := (isFiberedInGroupoids_comp_overMap_iff g p).2 h.isFiberedInGroupoids
  isom_isSheaf := by
    have : p.IsFibered := h.isFiberedInGroupoids.isFibered
    intro U' x y hx hy I Z f hcov Zij pr₁ pr₂ hZij xr yr xrij yrij φ hφfib hφiso hφγ
    obtain ⟨c, hcx⟩ : ∃ c : U'.left ⟶ V, p.obj x = Over.mk c := ⟨_, obj_eq_mk_of_overMap p g hx⟩
    obtain ⟨cy, hcy0⟩ : ∃ cy : U'.left ⟶ V, p.obj y = Over.mk cy := ⟨_, obj_eq_mk_of_overMap p g hy⟩
    have hcc : c = cy := by
      refine Over.eq_of_mem_over J Z f hcov _ _ fun i => ?_
      refine Over.hom_eq_of_mk_eq (Eq.trans (Restriction.obj_pt_eq p g hcx (xr i)).symm ?_)
      refine Eq.trans (obj_eq_of_fibreHom_overMap p g (xr i).hpt (yr i).hpt (φ i) (hφfib i)) ?_
      exact Restriction.obj_pt_eq p g hcy0 (yr i)
    have hcy : p.obj y = Over.mk c := hcc ▸ hcy0
    obtain ⟨G, ⟨hG₁, hG₂, hG₃⟩, hGu⟩ := h.isom_isSheaf x y hcx hcy
      (fun i => (Over.mk ((f i).left ≫ c) : Over V))
      (fun i => Over.homMk (f i).left rfl)
      (Over.mem_over_mk J c Z f hcov)
      (fun i j => (Over.mk ((pr₁ i j ≫ f i).left ≫ c) : Over V))
      (fun i j => Over.homMk (pr₁ i j).left (by simp))
      (fun i j => Over.homMk (pr₂ i j).left (by
        have hw := congrArg Over.Hom.left (hZij i j).w
        simp only [Over.comp_left] at hw
        simp only [Over.mk_hom, Over.comp_left, ← Category.assoc, hw]))
      (fun i j => Over.isPullback_mk (hZij i j) _ _ _ _ rfl rfl rfl rfl)
      (fun i => (xr i).descend p g (Restriction.obj_pt_eq p g hcx (xr i)) hcx
        (Over.OverMorphism.ext (by simp)))
      (fun i => (yr i).descend p g (Restriction.obj_pt_eq p g hcy (yr i)) hcy
        (Over.OverMorphism.ext (by simp)))
      (fun i j => (xrij i j).descend p g (Restriction.obj_pt_eq p g hcx (xrij i j)) hcx
        (Over.OverMorphism.ext (by simp)))
      (fun i j => (yrij i j).descend p g (Restriction.obj_pt_eq p g hcy (yrij i j)) hcy
        (Over.OverMorphism.ext (by simp)))
      φ
      (fun i => (fibreHom_comp_overMap_iff p g _ _ _ _ _ _ (φ i)).1 (hφfib i))
      hφiso
      (fun i j => by
        obtain ⟨γ, hγfib, hγ₁, hγ₂⟩ := hφγ i j
        refine ⟨γ, (fibreHom_comp_overMap_iff p g _ _ _ _ _ _ γ).1 hγfib, ?_, ?_⟩
        · exact (isRestrictionOf_descend_iff p g rfl rfl (xr i) (yr i) (xrij i j) (yrij i j)
            rfl rfl _ _ _ _ hcx hcy (Over.OverMorphism.ext (by simp))
            (Over.OverMorphism.ext (by simp)) (Over.OverMorphism.ext (by simp))
            (Over.OverMorphism.ext (by simp)) (Over.OverMorphism.ext (by simp))
            (Over.OverMorphism.ext (by simp)) (φ i) γ).1 hγ₁
        · exact (isRestrictionOf_descend_iff p g (hZij i j).w (hZij i j).w (xr j) (yr j)
            (xrij i j) (yrij i j) _ _ _ _ _ _ hcx hcy
            (Over.OverMorphism.ext (by simp)) (Over.OverMorphism.ext (by simp))
            (Over.OverMorphism.ext (by simp)) (Over.OverMorphism.ext (by simp))
            (Over.OverMorphism.ext (by simp)) (Over.OverMorphism.ext (by simp))
            (φ j) γ).1 hγ₂)
    refine ⟨G, ⟨?_, hG₂, hG₃⟩, fun G' hG' => hGu G' ⟨?_, hG'.2.1, hG'.2.2⟩⟩
    · exact (fibreHom_comp_overMap_iff p g x y hcx hcy hx hy G).2 hG₁
    · exact (fibreHom_comp_overMap_iff p g x y hcx hcy hx hy G').1 hG'.1
  effective_descent := by
    have : p.IsFibered := h.isFiberedInGroupoids.isFibered
    intro U' I Z f hcov Zij pr₁ pr₂ hZij Zijk s₁₂ s₂₃ hZijk q₁ q₂ q₃ hq₁ hq₂ hq₃ D
    have hwij : ∀ i j, pr₁ i j ≫ f i = pr₂ i j ≫ f j := fun i j => (hZij i j).w
    have hwq2 : ∀ i j k, q₁ i j k ≫ f i = q₂ i j k ≫ f j := fun i j k => by
      rw [hq₁, hq₂, Category.assoc, Category.assoc, hwij]
    have hwq3 : ∀ i j k, q₁ i j k ≫ f i = q₃ i j k ≫ f k := fun i j k => by
      rw [hq₁, hq₃, Category.assoc, Category.assoc, hwij i j, ← (hZij j k).w,
        ← Category.assoc, ← Category.assoc, (hZijk i j k).w]
    obtain ⟨a, ha⟩ : ∃ a : (∀ i, (Z i).left ⟶ V), ∀ i, p.obj (D.x i) = Over.mk (a i) :=
      ⟨_, fun i => obj_eq_mk_of_overMap p g (D.hx i)⟩
    have heZ : ∀ i, (Over.map g).obj (Over.mk (a i) : Over V) = Z i := fun i => by
      rw [← ha i]; exact D.hx i
    have haV : ∀ i, a i ≫ g = (Z i).hom := fun i => by
      have hw := Over.w (eqToHom (heZ i) : (Over.map g).obj (Over.mk (a i) : Over V) ⟶ Z i)
      simpa using hw.symm
    have hcompat : ∀ (i j : I) (Y : C) (u : Y ⟶ (Z i).left) (v : Y ⟶ (Z j).left),
        u ≫ (f i).left = v ≫ (f j).left → u ≫ a i = v ≫ a j := by
      intro i j Y u v huv
      have key : (pr₁ i j).left ≫ a i = (pr₂ i j).left ≫ a j :=
        Over.hom_eq_of_mk_eq ((Restriction.obj_pt_eq p g (ha i) (D.xrij i j)).symm.trans
          ((obj_eq_of_fibreHom_overMap p g (D.xrij i j).hpt (D.xrji i j).hpt (D.φ i j)
            (D.φ_fibreHom i j)).trans (Restriction.obj_pt_eq p g (ha j) (D.xrji i j))))
      have hP := (Over.isPullback_iff_left (pr₁ i j) (pr₂ i j) (f i) (f j) (hwij i j)).1
        (hZij i j)
      calc u ≫ a i = (hP.lift u v huv ≫ (pr₁ i j).left) ≫ a i := by rw [hP.lift_fst]
        _ = (hP.lift u v huv ≫ (pr₂ i j).left) ≫ a j := by
              rw [Category.assoc, Category.assoc, key]
        _ = v ≫ a j := by rw [hP.lift_snd]
    obtain ⟨c, hcg, hci⟩ := Over.exists_factorization_of_mem_over J g Z f hcov a haV hcompat
    have hx₀ : ∀ i, p.obj (D.x i) = (Over.mk ((f i).left ≫ c) : Over V) := fun i => by
      rw [hci i]; exact ha i
    have eU : (Over.map g).obj (Over.mk c : Over V) = U' :=
      CostructuredArrow.obj_ext _ _ rfl (by simpa using hcg.symm)
    have eZ : ∀ i, (Over.map g).obj (Over.mk ((f i).left ≫ c) : Over V) = Z i := fun i => by
      rw [← hx₀ i]; exact D.hx i
    have keyij : ∀ i j, (pr₂ i j).left ≫ (f j).left ≫ c
        = (pr₁ i j).left ≫ (f i).left ≫ c := fun i j =>
      Over.left_comp_comp_eq (hwij i j).symm c
    have keyq2 : ∀ i j k, (q₂ i j k).left ≫ (f j).left ≫ c
        = (q₁ i j k).left ≫ (f i).left ≫ c := fun i j k =>
      Over.left_comp_comp_eq (hwq2 i j k).symm c
    have keyq3 : ∀ i j k, (q₃ i j k).left ≫ (f k).left ≫ c
        = (q₁ i j k).left ≫ (f i).left ≫ c := fun i j k =>
      Over.left_comp_comp_eq (hwq3 i j k).symm c
    have hws23 : ∀ i j k, s₂₃ i j k ≫ pr₁ j k ≫ f j = q₁ i j k ≫ f i := fun i j k => by
      rw [← Category.assoc, ← (hZijk i j k).w, Category.assoc, hq₁, Category.assoc, hwij]
    have keys23 : ∀ i j k, (s₂₃ i j k).left ≫ (pr₁ j k).left ≫ (f j).left ≫ c
        = (q₁ i j k).left ≫ (f i).left ≫ c := fun i j k => by
      simpa using Over.left_comp_comp_eq (hws23 i j k) c
    have hAji : ∀ i j, p.obj (D.xrji i j).pt
        = (Over.mk ((pr₁ i j).left ≫ (f i).left ≫ c) : Over V) := fun i j => by
      rw [Restriction.obj_pt_eq p g (hx₀ j) (D.xrji i j), keyij i j]
    have hAwj : ∀ i j k, p.obj (D.wj i j k).pt
        = (Over.mk ((q₁ i j k).left ≫ (f i).left ≫ c) : Over V) := fun i j k => by
      rw [Restriction.obj_pt_eq p g (hx₀ j) (D.wj i j k), keyq2 i j k]
    have hAwk : ∀ i j k, p.obj (D.wk i j k).pt
        = (Over.mk ((q₁ i j k).left ≫ (f i).left ≫ c) : Over V) := fun i j k => by
      rw [Restriction.obj_pt_eq p g (hx₀ k) (D.wk i j k), keyq3 i j k]
    obtain ⟨xx, hxx, xrv, ψ, hψfib, hψiso, hψov⟩ := h.effective_descent
      (U := (Over.mk c : Over V))
      (fun i => (Over.mk ((f i).left ≫ c) : Over V))
      (fun i => Over.homMk (f i).left rfl)
      (Over.mem_over_mk J c Z f hcov)
      (fun i j => (Over.mk ((pr₁ i j).left ≫ (f i).left ≫ c) : Over V))
      (fun i j => Over.homMk (pr₁ i j).left rfl)
      (fun i j => Over.homMk (pr₂ i j).left (keyij i j))
      (fun i j => Over.isPullback_mk (hZij i j) _ _ _ _ rfl rfl rfl rfl)
      (fun i j k => (Over.mk ((q₁ i j k).left ≫ (f i).left ≫ c) : Over V))
      (fun i j k => Over.homMk (s₁₂ i j k).left (by simp [hq₁ i j k]))
      (fun i j k => Over.homMk (s₂₃ i j k).left (keys23 i j k))
      (fun i j k => Over.isPullback_mk (hZijk i j k) _ _ _ _ rfl rfl rfl rfl)
      (fun i j k => Over.homMk (q₁ i j k).left rfl)
      (fun i j k => Over.homMk (q₂ i j k).left (keyq2 i j k))
      (fun i j k => Over.homMk (q₃ i j k).left (keyq3 i j k))
      (fun i j k => Over.OverMorphism.ext (by
        simpa using congrArg Over.Hom.left (hq₁ i j k)))
      (fun i j k => Over.OverMorphism.ext (by
        simpa using congrArg Over.Hom.left (hq₂ i j k)))
      (fun i j k => Over.OverMorphism.ext (by
        simpa using congrArg Over.Hom.left (hq₃ i j k)))
      { x := D.x
        hx := hx₀
        xrij := fun i j => (D.xrij i j).descend p g
          (Restriction.obj_pt_eq p g (hx₀ i) (D.xrij i j)) (hx₀ i)
          (Over.OverMorphism.ext (by simp))
        xrji := fun i j => (D.xrji i j).descend p g (hAji i j) (hx₀ j)
          (Over.OverMorphism.ext (by simp))
        φ := D.φ
        φ_fibreHom := fun i j =>
          (fibreHom_comp_overMap_iff p g _ _ _ _ _ _ (D.φ i j)).1 (D.φ_fibreHom i j)
        φ_iso := D.φ_iso
        wi := fun i j k => (D.wi i j k).descend p g
          (Restriction.obj_pt_eq p g (hx₀ i) (D.wi i j k)) (hx₀ i)
          (Over.OverMorphism.ext (by simp))
        wj := fun i j k => (D.wj i j k).descend p g (hAwj i j k) (hx₀ j)
          (Over.OverMorphism.ext (by simp))
        wk := fun i j k => (D.wk i j k).descend p g (hAwk i j k) (hx₀ k)
          (Over.OverMorphism.ext (by simp))
        αij := D.αij
        αjk := D.αjk
        αik := D.αik
        αij_restr := fun i j k => (isRestrictionOf_descend_iff p g (hq₁ i j k) (hq₂ i j k)
          (D.xrij i j) (D.xrji i j) (D.wi i j k) (D.wj i j k) _ _ _ _ _ _ _ _ _ _ _ _
          (Over.OverMorphism.ext (by simp)) (Over.OverMorphism.ext (by simp))
          (D.φ i j) (D.αij i j k)).1 (D.αij_restr i j k)
        αjk_restr := fun i j k => (isRestrictionOf_descend_iff p g
          ((hq₂ i j k).trans (hZijk i j k).w) (hq₃ i j k)
          (D.xrij j k) (D.xrji j k) (D.wj i j k) (D.wk i j k) _ _ _ _ _ _ _ _ _ _ _ _
          (Over.OverMorphism.ext (by simp)) (Over.OverMorphism.ext (by simp))
          (D.φ j k) (D.αjk i j k)).1 (D.αjk_restr i j k)
        s₁₃ := fun i j k => Over.homMk (D.s₁₃ i j k).left (by simp [← D.hs₁₃₁ i j k])
        hs₁₃₁ := fun i j k => Over.OverMorphism.ext (by
          simpa using congrArg Over.Hom.left (D.hs₁₃₁ i j k))
        hs₁₃₂ := fun i j k => Over.OverMorphism.ext (by
          simpa using congrArg Over.Hom.left (D.hs₁₃₂ i j k))
        αik_restr := fun i j k => (isRestrictionOf_descend_iff p g (D.hs₁₃₁ i j k).symm
          (D.hs₁₃₂ i j k).symm (D.xrij i k) (D.xrji i k) (D.wi i j k) (D.wk i j k)
          _ _ _ _ _ _ _ _ _ _ _ _
          (Over.OverMorphism.ext (by simp)) (Over.OverMorphism.ext (by simp))
          (D.φ i k) (D.αik i j k)).1 (D.αik_restr i j k)
        cocycle := D.cocycle }
    have eZij : ∀ i j, (Over.map g).obj (Over.mk ((pr₁ i j).left ≫ (f i).left ≫ c) : Over V)
        = Zij i j := fun i j => by
      rw [← Restriction.obj_pt_eq p g (hx₀ i) (D.xrij i j)]; exact (D.xrij i j).hpt
    have hpf : (p ⋙ Over.map g).IsFibered :=
      ((isFiberedInGroupoids_comp_overMap_iff g p).2 h.isFiberedInGroupoids).isFibered
    have := hpf
    refine ⟨xx, (congrArg (Over.map g).obj hxx).trans eU,
      fun i => (xrv i).toOverMap p g (eZ i) eU (Over.OverMorphism.ext (by simp)) _, ψ, ?_,
      hψiso, ?_⟩
    · exact fun i => (fibreHom_comp_overMap_iff p g _ _ _ _ _ _ (ψ i)).2 (hψfib i)
    · intro i j
      obtain ⟨xrij, ψir, ψjr, hψir, hψjr, hir, hjr, hr₁, hr₂, hcomp⟩ := hψov i j
      refine ⟨xrij.toOverMap p g (eZij i j) eU (Over.OverMorphism.ext (by simp)) _,
        ψir, ψjr, ?_, ?_, hir, hjr, ?_, ?_, hcomp⟩
      · exact (fibreHom_comp_overMap_iff p g _ _ _ _ _ _ ψir).2 hψir
      · exact (fibreHom_comp_overMap_iff p g _ _ _ _ _ _ ψjr).2 hψjr
      · refine (isRestrictionOf_toOverMap_iff p g _ _ (xrv i)
          (Restriction.id p (D.x i) (hx₀ i)) xrij _ rfl
          (Category.comp_id (pr₁ i j)).symm (eZ i) (eZij i j) eU (eZ i)
          ?_ ?_ ?_ ?_ ?_ _ _ (ψ i) ψir).2 hr₁
        all_goals exact Over.OverMorphism.ext (by simp)
      · refine (isRestrictionOf_toOverMap_iff p g _ _ (xrv j)
          (Restriction.id p (D.x j) (hx₀ j)) xrij _ (hZij i j).w
          (Category.comp_id (pr₂ i j)).symm (eZ j) (eZij i j) eU (eZ j)
          ?_ ?_ ?_ ?_ ?_ _ _ (ψ j) ψjr).2 hr₂
        all_goals exact Over.OverMorphism.ext (by simp)

end Functor

end CategoryTheory

end
