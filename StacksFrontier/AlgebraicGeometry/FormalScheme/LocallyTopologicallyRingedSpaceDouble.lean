module

public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Limits
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsFull
public import StacksFrontier.AlgebraicGeometry.FormalScheme.LocallyTopologicallyRingedSpaceGlue

/-!
# Doubling a locally topologically ringed space along an open, with a twist

Let `X` be a locally topologically ringed space (an object of the category `LTRS` of Stacks
0AHY), `W ⊆ X` an open, and `φ` an automorphism of `X|_W` which is the identity on points but may
act nontrivially on sections. This file glues two copies of `X` along `W` by `φ`. The result
`𝔇` has `X ⊔ (X ∖ W)` as its set of points (the points of `W` are not doubled). A subset of `𝔇`
is open when its preimages in both copies are open. The sections of `𝒪_𝔇` over `U` are the pairs
`(s₀, s₁)` of sections of `𝒪_X` over the two preimages of `U` with `s₁|_W = φ^♯(s₀|_W)`, with
the topology induced from the product. Each copy is an open immersion `doubleι b : X ⟶ 𝔇`, and
on `W` the two copies differ exactly by `φ`. If `X` is a formal scheme, or is quasi-compact, then
so is `𝔇`.

## Main definitions

* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.double`: the double `𝔇` of `X` along `W`,
  twisted by `φ`, an object of `LTRS`.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.doubleι`: the inclusion of the `b`-th copy
  of `X`, for `b : Bool`.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.doubleOpen`: the open of `𝔇` which is the
  `b`-th copy, i.e. the range of `doubleι b`.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.doubleChartIso`: the isomorphism of the open
  subspace `doubleOpen b` with `X`.

## Main results

* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.isOpenImmersion_doubleι`: each `doubleι b`
  is an open immersion.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.doubleι_base_eq_iff`: two points of the
  copies agree in `𝔇` exactly when they are the same point of `X`, lying in `W` unless the
  copies are the same.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.ofRestrict_comp_doubleι_true`: the twist,
  `X|_W → X →(true) 𝔇` equals `X|_W →(φ) X|_W → X →(false) 𝔇`.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.isFormalScheme_double`: the double of a
  formal scheme is a formal scheme. There is also a `CompactSpace` instance for the double of a
  quasi-compact space.

## Implementation notes

Mathlib's `AlgebraicGeometry.SheafedSpace.GlueData` would need the pullback cocycle data of a
general gluing. Here there are only two pieces and the gluing map is the identity on points, so
the double is built by hand. Its space is the quotient of `Bool × X` by the relation identifying
`(b, x)` with `(b', x)` for `x ∈ W`, with the quotient topology. Its structure sheaf is the
equalizer, in presheaves of topological rings, of the two comparison maps
`ι₀_* 𝒪_X × ι₁_* 𝒪_X ⇉ j_* 𝒪_W`. The limits of `TopCommRingCat` (Stacks 0B23) are computed on
the subring of compatible families with the subspace topology of the product, so up to canonical
isomorphism this is the presheaf of pairs above. The sheaf condition in topological rings holds
because a limit of sheaves is a sheaf (`TopCat.isSheaf_of_isLimit`) and pushforwards of sheaves
are sheaves.
Over an open inside one copy, the other component of a section is determined by the first
through an isomorphism. This is
`AlgebraicGeometry.LocallyTopologicallyRingedSpace.isIso_comp_of_isEqualizer_of_isIso`, applied
after evaluating at the open (evaluation preserves limits), and it makes each `doubleι b` an open
immersion. The stalks of `𝔇` are then those of `X`, hence local.

## References

* [EGA I, Chapter I, Section 10]
* [Stacks Project, Section 87.2 (Tag 0AHY)](https://stacks.math.columbia.edu/tag/0AHY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Topology

universe u

namespace AlgebraicGeometry.LocallyTopologicallyRingedSpace

/-! ### The underlying space -/

section Space

variable (X : LTRS.{u}) (W : Opens X)

/-- The equivalence relation on `Bool × X` identifying `(b, x)` with `(b', x)` when `x ∈ W`:
the points of the two copies of `X` are glued along `W`. -/
def doubleSetoid : Setoid (Bool × X) where
  r p q := p.2 = q.2 ∧ (p.1 = q.1 ∨ p.2 ∈ W)
  iseqv :=
    { refl := fun _ => ⟨rfl, Or.inl rfl⟩
      symm := fun {p q} h => ⟨h.1.symm, h.2.imp Eq.symm fun hp => h.1 ▸ hp⟩
      trans := fun {p q r} h h' => ⟨h.1.trans h'.1, by
        rcases h.2 with h2 | h2
        · rcases h'.2 with h3 | h3
          · exact Or.inl (h2.trans h3)
          · exact Or.inr (h.1 ▸ h3)
        · exact Or.inr h2⟩ }

/-- The underlying space of the double of `X` along `W`: two copies of `X` glued along `W`,
with the quotient topology. -/
def doubleSpace : TopCat.{u} := TopCat.of (Quotient (doubleSetoid X W))

/-- The inclusion of the `b`-th copy of `X` into the double. -/
def doubleSpaceι (b : Bool) : X.carrier ⟶ doubleSpace X W :=
  TopCat.ofHom ⟨fun x => Quotient.mk (doubleSetoid X W) (b, x),
    continuous_quotient_mk'.comp (continuous_const.prodMk continuous_id)⟩

/-- On points, the inclusion of the `b`-th copy sends `x` to the class of `(b, x)`. -/
theorem doubleSpaceι_apply (b : Bool) (x : X) :
    doubleSpaceι X W b x = Quotient.mk (doubleSetoid X W) (b, x) := rfl

/-- Two points of the two copies of `X` agree in the double exactly when they are the same point
of `X`, which lies in `W` unless the copies are the same. -/
theorem doubleSpaceι_eq_iff {b b' : Bool} {x x' : X} :
    doubleSpaceι X W b x = doubleSpaceι X W b' x' ↔ x = x' ∧ (b = b' ∨ x ∈ W) :=
  Quotient.eq (r := doubleSetoid X W)

/-- Every point of the double lies in one of the two copies of `X`. -/
theorem exists_doubleSpaceι_eq (y : doubleSpace X W) : ∃ b x, doubleSpaceι X W b x = y := by
  obtain ⟨⟨b, x⟩, rfl⟩ := Quotient.exists_rep (s := doubleSetoid X W) y
  exact ⟨b, x, rfl⟩

/-- A subset of the double is open exactly when its preimages in both copies of `X` are. -/
theorem isOpen_doubleSpace_iff (S : Set (doubleSpace X W)) :
    IsOpen S ↔ ∀ b, IsOpen (doubleSpaceι X W b ⁻¹' S) := by
  refine ⟨fun hS b => hS.preimage (doubleSpaceι X W b).hom.continuous, fun hS => ?_⟩
  show IsOpen (Quotient.mk (doubleSetoid X W) ⁻¹' S)
  have : Quotient.mk (doubleSetoid X W) ⁻¹' S =
      ⋃ b, ({b} : Set Bool) ×ˢ (doubleSpaceι X W b ⁻¹' S) := by
    ext ⟨b, x⟩
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff]
    exact ⟨fun h => ⟨b, rfl, h⟩, fun ⟨_, rfl, h⟩ => h⟩
  rw [this]
  exact isOpen_iUnion fun b => (isOpen_discrete _).prod (hS b)

/-- The preimage in the `b'`-th copy of the image of the `b`-th copy of a subset `U`. -/
theorem mem_preimage_doubleSpaceι_image_iff {b b' : Bool} {U : Set X} {x : X} :
    x ∈ doubleSpaceι X W b' ⁻¹' (doubleSpaceι X W b '' U) ↔ x ∈ U ∧ (b = b' ∨ x ∈ W) := by
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨y, hy, h⟩
    obtain ⟨rfl, h'⟩ := (doubleSpaceι_eq_iff X W).mp h
    exact ⟨hy, h'⟩
  · rintro ⟨hx, h⟩
    exact ⟨x, hx, (doubleSpaceι_eq_iff X W).mpr ⟨rfl, h⟩⟩

/-- Each copy of `X` is an open subspace of the double. -/
theorem isOpenEmbedding_doubleSpaceι (b : Bool) : IsOpenEmbedding (doubleSpaceι X W b) := by
  refine .of_continuous_injective_isOpenMap (doubleSpaceι X W b).hom.continuous
    (fun x x' h => ((doubleSpaceι_eq_iff X W).mp h).1) fun U hU => ?_
  rw [isOpen_doubleSpace_iff]
  intro b'
  have : doubleSpaceι X W b' ⁻¹' (doubleSpaceι X W b '' U) =
      U ∩ (if b = b' then Set.univ else W) := by
    ext x
    rw [mem_preimage_doubleSpaceι_image_iff]
    split_ifs with h <;> simp [h]
  rw [this]
  split_ifs
  · exact hU.inter isOpen_univ
  · exact hU.inter W.isOpen

end Space

/-! ### A criterion for a leg of an equalizer of a product to be an isomorphism -/

/-- Let `e : E ⟶ P` be an equalizer of `p₁ ≫ u` and `p₂ ≫ v`, where `p₁, p₂` exhibit `P` as a
product of `A₁` and `A₂`. If `v` is an isomorphism, then `e ≫ p₁ : E ⟶ A₁` is an isomorphism:
the second component of a point of `E` is determined by the first. The hypotheses are the parts
of the two universal properties that the argument uses. -/
theorem isIso_comp_of_isEqualizer_of_isIso {C : Type*} [Category* C] {E P A₁ A₂ Q : C}
    (e : E ⟶ P) (he : Mono e) (p₁ : P ⟶ A₁) (p₂ : P ⟶ A₂) (u : A₁ ⟶ Q) (v : A₂ ⟶ Q)
    (hv : IsIso v)
    (hlift : ∃ l : A₁ ⟶ P, l ≫ p₁ = 𝟙 _ ∧ l ≫ p₂ = u ≫ inv v)
    (hext : ∀ x y : E ⟶ P, x ≫ p₁ = y ≫ p₁ → x ≫ p₂ = y ≫ p₂ → x = y)
    (hfac : ∀ l : A₁ ⟶ P, l ≫ p₁ ≫ u = l ≫ p₂ ≫ v → ∃ m, m ≫ e = l)
    (w : e ≫ p₁ ≫ u = e ≫ p₂ ≫ v) : IsIso (e ≫ p₁) := by
  obtain ⟨l, hl₁, hl₂⟩ := hlift
  obtain ⟨m, hm⟩ := hfac l (by simp [reassoc_of% hl₁, reassoc_of% hl₂])
  refine ⟨m, ?_, by rw [reassoc_of% hm, hl₁]⟩
  rw [← cancel_mono e, Category.id_comp]
  apply hext
  · simp only [Category.assoc, reassoc_of% hm, hl₁, Category.comp_id]
  · simp only [Category.assoc, reassoc_of% hm, hl₂]
    rw [reassoc_of% w, IsIso.hom_inv_id, Category.comp_id]

/-! ### The structure sheaf -/

section Sheaf

variable (X : LTRS.{u}) (W : Opens X) (φ : X.restrict W ≅ X.restrict W)
  (hφ : ∀ x, φ.hom.toHom.base x = x)

/-- The pushforward of `𝒪_X` along the inclusion of the `b`-th copy of `X` into the double. -/
abbrev doubleSummand (b : Bool) : (doubleSpace X W).Presheaf TopCommRingCat.{u} :=
  doubleSpaceι X W b _* X.presheaf

include hφ in
/-- On points, the twist `φ` followed by the inclusion of `W` into the copy `false` agrees with
the inclusion of `W` into the copy `true`. -/
theorem doubleSpaceι_twist :
    φ.hom.toHom.base ≫ (X.ofRestrict W).toHom.base ≫ doubleSpaceι X W false =
      (X.ofRestrict W).toHom.base ≫ doubleSpaceι X W true := by
  ext x
  show doubleSpaceι X W false (φ.hom.toHom.base x).1 = doubleSpaceι X W true x.1
  rw [hφ x, doubleSpaceι_eq_iff]
  exact ⟨rfl, Or.inr x.2⟩

/-- The pushforward of `𝒪_W` along the inclusion of `W` into the copy `true` of the double:
the presheaf in which the two copies of a section are compared. -/
abbrev doubleOverlap : (doubleSpace X W).Presheaf TopCommRingCat.{u} :=
  ((X.ofRestrict W).toHom.base ≫ doubleSpaceι X W true) _* (X.restrict W).presheaf

/-- The comparison of the component `false` of a section, before projecting: restrict it to `W`
and apply the twist `φ^♯`. -/
noncomputable def doubleTwistMap : doubleSummand X W false ⟶ doubleOverlap X W :=
  (TopCat.Presheaf.pushforward _ (doubleSpaceι X W false)).map
      ((X.ofRestrict W).toHom.c ≫
        (TopCat.Presheaf.pushforward _ (X.ofRestrict W).toHom.base).map φ.hom.toHom.c) ≫
    (TopCat.Presheaf.Pushforward.comp _ _ _).inv ≫ (TopCat.Presheaf.Pushforward.comp _ _ _).inv ≫
    (TopCat.Presheaf.pushforwardEq (doubleSpaceι_twist X W φ hφ) (X.restrict W).presheaf).hom

/-- The comparison of the component `true` of a section, before projecting: restrict it to
`W`. -/
noncomputable def doubleRestrictMap : doubleSummand X W true ⟶ doubleOverlap X W :=
  (TopCat.Presheaf.pushforward _ (doubleSpaceι X W true)).map (X.ofRestrict W).toHom.c ≫
    (TopCat.Presheaf.Pushforward.comp _ _ _).inv

/-- The comparison of the copy `false` of a section: restrict it to `W` and apply the twist
`φ^♯`. -/
noncomputable def doubleTwistLeg : ∏ᶜ doubleSummand X W ⟶ doubleOverlap X W :=
  Pi.π (doubleSummand X W) false ≫ doubleTwistMap X W φ hφ

/-- The comparison of the copy `true` of a section: restrict it to `W`. -/
noncomputable def doubleRestrictLeg : ∏ᶜ doubleSummand X W ⟶ doubleOverlap X W :=
  Pi.π (doubleSummand X W) true ≫ doubleRestrictMap X W

/-- The structure presheaf of the double: pairs `(s₀, s₁)` of sections of `𝒪_X` over the
preimages of an open in the two copies with `s₁|_W = φ^♯(s₀|_W)`, i.e. the equalizer of
`AlgebraicGeometry.LocallyTopologicallyRingedSpace.doubleTwistLeg` and
`AlgebraicGeometry.LocallyTopologicallyRingedSpace.doubleRestrictLeg`. -/
noncomputable abbrev doublePresheaf : (doubleSpace X W).Presheaf TopCommRingCat.{u} :=
  equalizer (doubleTwistLeg X W φ hφ) (doubleRestrictLeg X W)

/-- The structure presheaf of the double is a sheaf of topological rings, as an equalizer of a
product of pushforwards of sheaves and a pushforward of a sheaf. -/
theorem doublePresheaf_isSheaf : (doublePresheaf X W φ hφ).IsSheaf := by
  have hP : (∏ᶜ doubleSummand X W).IsSheaf :=
    TopCat.isSheaf_of_isLimit (Discrete.functor (doubleSummand X W))
      (fun b => TopCat.Sheaf.pushforward_sheaf_of_sheaf _ X.IsSheaf) (limit.isLimit _)
  have hQ : (doubleOverlap X W).IsSheaf :=
    TopCat.Sheaf.pushforward_sheaf_of_sheaf _ (X.restrict W).IsSheaf
  refine TopCat.isSheaf_of_isLimit
    (parallelPair (doubleTwistLeg X W φ hφ) (doubleRestrictLeg X W)) ?_ (limit.isLimit _)
  rintro (_ | _)
  exacts [hP, hQ]

/-- The double of `X` along `W` twisted by `φ`, as a sheafed space of topological rings. -/
noncomputable def doubleSheafedSpace : SheafedSpace TopCommRingCat.{u} where
  carrier := doubleSpace X W
  presheaf := doublePresheaf X W φ hφ
  IsSheaf := doublePresheaf_isSheaf X W φ hφ

/-- The inclusion of the `b`-th copy of `X` into the double, as a morphism of presheafed
spaces: on sections it takes the `b`-th component. -/
noncomputable def doubleιHom (b : Bool) :
    X.toPresheafedSpace ⟶ (doubleSheafedSpace X W φ hφ).toPresheafedSpace where
  base := doubleSpaceι X W b
  c := equalizer.ι (doubleTwistLeg X W φ hφ) (doubleRestrictLeg X W) ≫
    Pi.π (doubleSummand X W) b

end Sheaf

/-! ### The inclusions of the two copies are open immersions -/

section OpenImmersion

variable (X : LTRS.{u}) (W : Opens X) (φ : X.restrict W ≅ X.restrict W)
  (hφ : ∀ x, φ.hom.toHom.base x = x)

/-- The image of one copy of `X` meets the other copy inside `W`. -/
theorem preimage_doubleSpaceι_image_subset {b b' : Bool} (h : b ≠ b') (U : Set X) :
    doubleSpaceι X W b' ⁻¹' (doubleSpaceι X W b '' U) ⊆ W := fun _ hx =>
  (((mem_preimage_doubleSpaceι_image_iff X W).mp hx).2.resolve_left h)

/-- The underlying morphism of presheafed spaces of an isomorphism of `LTRS` is an
isomorphism. -/
theorem isIso_toHom_of_iso {Y Z : LTRS.{u}} (e : Y ≅ Z) :
    IsIso (X := Y.toPresheafedSpace) (Y := Z.toPresheafedSpace) e.hom.toHom :=
  ⟨⟨e.inv.toHom, congrArg Hom.toHom e.hom_inv_id, congrArg Hom.toHom e.inv_hom_id⟩⟩

/-- Over an open whose preimage in the copy `false` lies in `W`, the comparison of the component
`false` is an isomorphism. -/
theorem isIso_doubleTwistMap_app {V : Opens (doubleSpace X W)}
    (hV : (Opens.map (doubleSpaceι X W false)).obj V ≤ W) :
    IsIso ((doubleTwistMap X W φ hφ).app (op V)) := by
  have : IsIso ((X.ofRestrict W).toHom.c.app (op ((Opens.map (doubleSpaceι X W false)).obj V))) :=
    AlgebraicGeometry.isIso_ofRestrict_c_app W hV
  have := isIso_toHom_of_iso φ
  rw [doubleTwistMap, NatTrans.comp_app, TopCat.Presheaf.pushforward_map_app', NatTrans.comp_app]
  infer_instance

/-- Over an open whose preimage in the copy `true` lies in `W`, the comparison of the component
`true` is an isomorphism. -/
theorem isIso_doubleRestrictMap_app {V : Opens (doubleSpace X W)}
    (hV : (Opens.map (doubleSpaceι X W true)).obj V ≤ W) :
    IsIso ((doubleRestrictMap X W).app (op V)) := by
  have : IsIso ((X.ofRestrict W).toHom.c.app (op ((Opens.map (doubleSpaceι X W true)).obj V))) :=
    AlgebraicGeometry.isIso_ofRestrict_c_app W hV
  rw [doubleRestrictMap, NatTrans.comp_app, TopCat.Presheaf.pushforward_map_app']
  infer_instance

/-- Over an open of the double whose preimage in the copy `!b` lies in `W`, the map on sections
of the inclusion of the copy `b` is an isomorphism: a section of the double there is determined
by its `b`-th component, the other one being its image under the comparison maps. -/
theorem isIso_doubleιHom_c_app (b : Bool) (V : Opens (doubleSpace X W))
    (hV : (Opens.map (doubleSpaceι X W (!b))).obj V ≤ W) :
    IsIso ((doubleιHom X W φ hφ b).c.app (op V)) := by
  let ev := (evaluation (Opens (doubleSpace X W))ᵒᵖ TopCommRingCat.{u}).obj (op V)
  have hE := isLimitForkMapOfIsLimit ev
    (equalizer.condition (doubleTwistLeg X W φ hφ) (doubleRestrictLeg X W))
    (equalizerIsEqualizer _ _)
  have hP := isLimitFanMkObjOfIsLimit ev _ _ (productIsProduct (doubleSummand X W))
  let m : ∀ c, doubleSummand X W c ⟶ doubleOverlap X W :=
    Bool.rec (doubleTwistMap X W φ hφ) (doubleRestrictMap X W)
  have w := congr_app
    (equalizer.condition (doubleTwistLeg X W φ hφ) (doubleRestrictLeg X W)) (op V)
  have key : ∀ c, IsIso ((m (!c)).app (op V)) → IsIso ((equalizer.ι (doubleTwistLeg X W φ hφ)
      (doubleRestrictLeg X W)).app (op V) ≫ (Pi.π (doubleSummand X W) c).app (op V)) := by
    intro c hv
    refine isIso_comp_of_isEqualizer_of_isIso _ (Fork.IsLimit.mono hE) _
      ((Pi.π (doubleSummand X W) (!c)).app (op V)) ((m c).app (op V))
      ((m (!c)).app (op V)) hv ?_ ?_ (fun l hl => ?_) ?_
    · generalize (m c).app (op V) ≫ @inv _ _ _ _ ((m (!c)).app (op V)) hv = g
      cases c
      exacts [⟨hP.lift (Fan.mk _ fun | false => 𝟙 _ | true => g),
        hP.fac _ ⟨false⟩, hP.fac _ ⟨true⟩⟩,
        ⟨hP.lift (Fan.mk _ fun | false => g | true => 𝟙 _),
        hP.fac _ ⟨true⟩, hP.fac _ ⟨false⟩⟩]
    · intro x y h₁ h₂
      refine hP.hom_ext ?_
      rintro ⟨d⟩
      cases c <;> cases d
      exacts [h₁, h₂, h₂, h₁]
    · exact ⟨_, (Fork.IsLimit.lift' hE l (by cases c; exacts [hl, hl.symm])).2⟩
    · cases c
      exacts [w, w.symm]
  cases b
  · exact key false (isIso_doubleRestrictMap_app X W (V := V) hV)
  · exact key true (isIso_doubleTwistMap_app X W φ hφ (V := V) hV)

/-- The inclusion of each copy of `X` into the double is an open immersion of presheafed
spaces. -/
instance isOpenImmersion_doubleιHom (b : Bool) :
    PresheafedSpace.IsOpenImmersion (doubleιHom X W φ hφ b) where
  base_open := isOpenEmbedding_doubleSpaceι X W b
  c_iso U := isIso_doubleιHom_c_app X W φ hφ b _
    (preimage_doubleSpaceι_image_subset X W (by cases b <;> decide) _)

end OpenImmersion

/-! ### The double as a locally topologically ringed space -/

section Double

variable (X : LTRS.{u}) (W : Opens X) (φ : X.restrict W ≅ X.restrict W)
  (hφ : ∀ x, φ.hom.toHom.base x = x)

/-- **The double of `X` along `W`, twisted by `φ`.** Two copies of `X` glued along the open `W`
by the automorphism `φ` of `X|_W`, which is the identity on points: as a set it is
`X ⊔ (X ∖ W)`, a subset is open when its preimages in both copies are, and the sections over
`U` are the pairs `(s₀, s₁)` of sections of `𝒪_X` over the two preimages of `U` with
`s₁|_W = φ^♯(s₀|_W)`, carrying the topology induced from the product. Its stalks are those of
`X`, so it is a locally topologically ringed space. -/
noncomputable def double : LTRS.{u} where
  toSheafedSpace := doubleSheafedSpace X W φ hφ
  isLocalRing y := by
    obtain ⟨b, x, rfl⟩ := exists_doubleSpaceι_eq X W y
    have := PresheafedSpace.IsOpenImmersion.stalk_iso (doubleιHom X W φ hφ b) x
    exact (TopCommRingCat.ringEquivOfIso
      (asIso ((doubleιHom X W φ hφ b).stalkMap x))).symm.isLocalRing

/-- The inclusion of the `b`-th copy of `X` into the double, a morphism of `LTRS`: its stalk maps
are isomorphisms, hence local. -/
noncomputable def doubleι (b : Bool) : X ⟶ double X W φ hφ where
  toHom := doubleιHom X W φ hφ b
  isLocalHom x :=
    @TopCommRingCat.isLocalHom_val_of_isIso _ _ _
      (PresheafedSpace.IsOpenImmersion.stalk_iso (doubleιHom X W φ hφ b) x)

/-- The inclusion of each copy of `X` into the double is an open immersion. -/
instance isOpenImmersion_doubleι (b : Bool) :
    PresheafedSpace.IsOpenImmersion (doubleι X W φ hφ b).toHom :=
  isOpenImmersion_doubleιHom X W φ hφ b

/-- On points, the inclusion of the `b`-th copy of `X` into the double. -/
theorem doubleι_base_apply (b : Bool) (x : X) :
    (doubleι X W φ hφ b).toHom.base x = doubleSpaceι X W b x := rfl

/-- Each copy of `X` is mapped injectively into the double. -/
theorem doubleι_base_injective (b : Bool) :
    Function.Injective (doubleι X W φ hφ b).toHom.base :=
  fun _ _ h => ((doubleSpaceι_eq_iff X W).mp h).1

/-- Two points of the two copies of `X` agree in the double exactly when they are the same point
of `X`, lying in `W` unless the copies are the same: the points of `W` are not doubled. -/
theorem doubleι_base_eq_iff {b b' : Bool} {x x' : X} :
    (doubleι X W φ hφ b).toHom.base x = (doubleι X W φ hφ b').toHom.base x' ↔
      x = x' ∧ (b = b' ∨ x ∈ W) :=
  doubleSpaceι_eq_iff X W

/-- Every point of the double lies in one of the two copies of `X`. -/
theorem exists_doubleι_base_eq (y : double X W φ hφ) :
    ∃ b x, (doubleι X W φ hφ b).toHom.base x = y :=
  exists_doubleSpaceι_eq X W y

/-- **The twist.** On `W` the two inclusions of `X` into the double differ by `φ`: restricting
the copy `true` to `W` is restricting the copy `false` to `W` after applying `φ`. -/
theorem ofRestrict_comp_doubleι_true :
    X.ofRestrict W ≫ doubleι X W φ hφ true = φ.hom ≫ X.ofRestrict W ≫ doubleι X W φ hφ false := by
  refine Hom.ext' ?_
  rw [comp_toHom, comp_toHom, comp_toHom]
  refine (PresheafedSpace.ext _ _ (doubleSpaceι_twist X W φ hφ) ?_).symm
  refine NatTrans.ext (funext fun U => ?_)
  have h := congr_app (equalizer.condition (doubleTwistLeg X W φ hφ) (doubleRestrictLeg X W)) U
  exact h

/-- The open of the double which is the `b`-th copy of `X`: the range of `doubleι b`. -/
def doubleOpen (b : Bool) : Opens (double X W φ hφ) :=
  ⟨Set.range (doubleSpaceι X W b), (isOpenEmbedding_doubleSpaceι X W b).isOpen_range⟩

/-- The open `doubleOpen b` is the range of the inclusion of the `b`-th copy of `X`. -/
theorem coe_doubleOpen (b : Bool) :
    (doubleOpen X W φ hφ b : Set (double X W φ hφ)) = Set.range (doubleι X W φ hφ b).toHom.base :=
  rfl

/-- **The charts of the double.** The open subspace `doubleOpen b` of the double is isomorphic,
as a presheafed space of topological rings, to `X`, by the inclusion of the `b`-th copy. -/
noncomputable def doubleChartIso (b : Bool) :
    (double X W φ hφ).toPresheafedSpace.restrict (f := (doubleOpen X W φ hφ b).inclusion')
      (doubleOpen X W φ hφ b).isOpenEmbedding' ≅ X.toPresheafedSpace :=
  haveI := PresheafedSpace.IsOpenImmersion.ofRestrict (double X W φ hφ).toPresheafedSpace
    (f := (doubleOpen X W φ hφ b).inclusion') (doubleOpen X W φ hφ b).isOpenEmbedding'
  PresheafedSpace.IsOpenImmersion.isoOfRangeEq
    ((double X W φ hφ).toPresheafedSpace.ofRestrict (f := (doubleOpen X W φ hφ b).inclusion')
      (doubleOpen X W φ hφ b).isOpenEmbedding')
    (doubleι X W φ hφ b).toHom Subtype.range_coe

/-- The inverse of the chart isomorphism, followed by the inclusion of `doubleOpen b`, is the
inclusion of the `b`-th copy of `X`. -/
theorem doubleChartIso_inv_comp_ofRestrict (b : Bool) :
    (doubleChartIso X W φ hφ b).inv ≫ (double X W φ hφ).toPresheafedSpace.ofRestrict
      (doubleOpen X W φ hφ b).isOpenEmbedding' = (doubleι X W φ hφ b).toHom := by
  have := PresheafedSpace.IsOpenImmersion.ofRestrict (double X W φ hφ).toPresheafedSpace
    (f := (doubleOpen X W φ hφ b).inclusion') (doubleOpen X W φ hφ b).isOpenEmbedding'
  exact PresheafedSpace.IsOpenImmersion.lift_fac
    ((double X W φ hφ).toPresheafedSpace.ofRestrict (f := (doubleOpen X W φ hφ b).inclusion')
      (doubleOpen X W φ hφ b).isOpenEmbedding') (doubleι X W φ hφ b).toHom
    (le_of_eq Subtype.range_coe.symm)

/-- **The double of a formal scheme is a formal scheme.** An affine formal open neighbourhood of
a point of the `b`-th copy of `X` is carried by the open immersion `doubleι b` to one of its
image in the double. -/
theorem isFormalScheme_double (hX : IsFormalScheme X) : IsFormalScheme (double X W φ hφ) := by
  intro y
  obtain ⟨b, x, rfl⟩ := exists_doubleι_base_eq X W φ hφ y
  obtain ⟨U, hxU, A, hlin, hA, ⟨χ⟩⟩ := hX x
  let V : Opens (double X W φ hφ) :=
    (PresheafedSpace.IsOpenImmersion.base_open (f := (doubleι X W φ hφ b).toHom)).functor.obj U
  have e : Set.range ((double X W φ hφ).toPresheafedSpace.ofRestrict (f := V.inclusion')
        V.isOpenEmbedding').base =
      Set.range (X.toPresheafedSpace.ofRestrict (f := U.inclusion') U.isOpenEmbedding' ≫
        (doubleι X W φ hφ b).toHom).base := by
    ext z
    simp only [PresheafedSpace.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp, Set.range_comp]
    show z ∈ Set.range Subtype.val ↔ z ∈ _ '' Set.range Subtype.val
    rw [Subtype.range_coe, Subtype.range_coe]
    rfl
  have := PresheafedSpace.IsOpenImmersion.ofRestrict (double X W φ hφ).toPresheafedSpace
    (f := V.inclusion') V.isOpenEmbedding'
  have := PresheafedSpace.IsOpenImmersion.ofRestrict X.toPresheafedSpace
    (f := U.inclusion') U.isOpenEmbedding'
  exact ⟨V, ⟨x, hxU, rfl⟩, A, hlin, hA,
    ⟨PresheafedSpace.IsOpenImmersion.isoOfRangeEq _ _ e ≪≫ χ⟩⟩

/-- The double of a quasi-compact space is quasi-compact: it is the image of two copies. -/
instance compactSpace_double [CompactSpace X] : CompactSpace (double X W φ hφ) :=
  inferInstanceAs (CompactSpace (Quotient (doubleSetoid X W)))

end Double


end AlgebraicGeometry.LocallyTopologicallyRingedSpace

end
