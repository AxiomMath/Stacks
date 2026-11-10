module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.Constant
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale

/-!
# Constant sheaves on a site of schemes

Let `G` be an abstract group and let `S` be a scheme. For any Grothendieck topology `J` on the
schemes over `S` which is finer than the Zariski topology and coarser than the fpqc topology,
the sheafification of the constant presheaf with value `G` has the Zariski locally constant
`G`-valued maps as its sections. Consequently the canonical comparison from the Zariski
sheafification to the `J`-sheafification is an isomorphism, and the constant sheaf is the
functor of points of the constant group scheme `G_S`.

This file also isolates the part of the argument which only depends on a functor `F` from a
site to schemes: if every open cover of `F.obj T` can be realised by a `J`-covering family of
`T`, and `F.op` composed with the locally constant maps is a `J`-sheaf, then the constant
`J`-sheaf is that presheaf of locally constant maps. The individual big and small sites of a
scheme are treated in the sibling files of the surrounding directory.

## Main definitions

* `AlgebraicGeometry.constantToLocallyConstantMapsOver` — the canonical map from the constant
  presheaf on the schemes over `S` to the presheaf of locally constant maps.
* `AlgebraicGeometry.constantToLocallyConstantMapsOn` — the same map along a functor to
  schemes.
* `AlgebraicGeometry.zariskiSheafToTauSheaf` — the comparison between the sheafifications for
  two nested topologies, induced by the two sheafification units.
* `AlgebraicGeometry.ConstantSheafIso.UnitCompatible` — the property of an identification of a
  constant sheaf with locally constant maps that it sends a constant presheaf section to the
  corresponding constant map.

## Main results

* `AlgebraicGeometry.constantSheafIsoLocallyConstantMaps` identifies the sheafification of the
  constant presheaf on the schemes over `S` for every topology between the Zariski and the
  fpqc topology, and `constantSheafIsoLocallyConstantMaps_unit` fixes that identification by
  its action on constant sections.
* `AlgebraicGeometry.constantSheafComparison_isIso` — the canonical comparison from the
  Zariski sheafification of the constant presheaf to its `J`-sheafification is invertible.
* `AlgebraicGeometry.constantSheafIsoConstantGroupSchemePoints` identifies the constant sheaf
  with the underlying presheaf of the group-valued functor of points of `G_S`.
* `AlgebraicGeometry.constantSheafIsoLocallyConstantMapsOn` and
  `constantSheafIsoLocallyConstantMapsOn_unit` are the corresponding statements along a
  functor from an arbitrary site to schemes.

## Implementation notes

The identification is an isomorphism of presheaves, not merely a family of bijections of
sections, so it includes compatibility with the restriction maps. The group is placed in the
common universe of the site and of the value category; its smallness relative to the universe
of schemes is the representability condition for the constant group scheme. The comparison
result identifies the canonical map rather than merely asserting that some isomorphism exists,
and the unit statements likewise pin down the identification instead of leaving it arbitrary.

The sites of schemes have morphisms one universe below their objects, while the group of
sections lives in a possibly larger universe. The standard sheafification instances are stated
at the universe of the site, so `AlgebraicGeometry.hasSheafify_grpCat` and its companions
transport them to the universe used here.

## References

* [Stacks Project, Tag 03P5](https://stacks.math.columbia.edu/tag/03P5)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry

/-! ### Universe transport for the sheafification instances -/

/-- Filtered colimits of groups exist at any universe, in particular at a universe larger than
the one in which the shape lives. -/
public theorem grpCatHasFilteredColimitsOfShape (D : Type w) [SmallCategory D] [IsFiltered D] :
    Limits.HasColimitsOfShape D GrpCat.{w} where
  has_colimit F := ⟨⟨GrpCat.FilteredColimits.colimitCocone F,
    GrpCat.FilteredColimits.colimitCoconeIsColimit F⟩⟩

attribute [local instance] grpCatHasFilteredColimitsOfShape

/-- On an essentially small site the local isomorphisms of presheaves of types in a larger
universe are exactly the locally bijective morphisms. -/
public theorem wEqualsLocallyBijective_type {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) :
    J.WEqualsLocallyBijective (Type (max (u + 1) v)) := by
  let : UnivLE.{u, u + 1} := univLE_max.{u, u + 1}
  let : UnivLE.{u + 1, max (u + 1) v} := univLE_max.{u + 1, v}
  let : UnivLE.{u, max (u + 1) v} := UnivLE.trans.{u, u + 1, max (u + 1) v}
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, max (u + 1) v,
    u + 1, max (u + 1) v + 1, max (u + 1) v} (J := J) (A := Type (max (u + 1) v))

/-- Sheaves of groups in a larger universe on an essentially small site have a sheafification. -/
public theorem hasSheafify_grpCat {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) :
    HasSheafify J GrpCat.{max (u + 1) v} := by
  let : UnivLE.{u, u + 1} := univLE_max.{u, u + 1}
  let : UnivLE.{u + 1, max (u + 1) v} := univLE_max.{u + 1, v}
  let : UnivLE.{u, max (u + 1) v} := UnivLE.trans.{u, u + 1, max (u + 1) v}
  exact hasSheafifyEssentiallySmallSite.{u, max (u + 1) v,
    u + 1, max (u + 1) v + 1, max (u + 1) v} J GrpCat.{max (u + 1) v}

/-- On an essentially small site the local isomorphisms of presheaves of groups in a larger
universe are exactly the locally bijective morphisms. -/
public theorem wEqualsLocallyBijective_grpCat {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) :
    J.WEqualsLocallyBijective GrpCat.{max (u + 1) v} := by
  let : UnivLE.{u, u + 1} := univLE_max.{u, u + 1}
  let : UnivLE.{u + 1, max (u + 1) v} := univLE_max.{u + 1, v}
  let : UnivLE.{u, max (u + 1) v} := UnivLE.trans.{u, u + 1, max (u + 1) v}
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, max (u + 1) v,
    u + 1, max (u + 1) v + 1, max (u + 1) v} (J := J) (A := GrpCat.{max (u + 1) v})

/-! ### Locally constant maps as a sheaf -/

/-- The map sending `g : G` to the constant map with value `g`, from the constant presheaf on
the schemes over `S` to the presheaf of locally constant `G`-valued maps. -/
public def constantToLocallyConstantMapsOver (S : Scheme.{u}) (G : Type (max (u + 1) v))
    [Group G] :
    (Functor.const (Over S)ᵒᵖ).obj G ⟶ (locallyConstantMapsOver G S ⋙ forget GrpCat) where
  app T := ↾(fun g => LocallyConstant.const T.unop.left g)
  naturality X Y f := by
    ext g
    rfl

/-- For a discrete group `G`, the locally constant `G`-valued maps on the schemes over `S` are
the continuous `G`-valued maps on the underlying schemes. -/
public def locallyConstantMapsOverIsoContinuousMaps (S : Scheme.{u})
    (G : Type (max (u + 1) v)) [Group G] [TopologicalSpace G] [DiscreteTopology G] :
    (locallyConstantMapsOver G S ⋙ forget GrpCat) ≅
      (Over.forget S).op ⋙ continuousMapPresheaf G := by
  refine NatIso.ofComponents (fun T => Equiv.toIso {
    toFun := fun (f : LocallyConstant T.unop.left G) => f.toContinuousMap
    invFun := fun (f : C(T.unop.left, G)) =>
      ⟨(f : T.unop.left → G),
        (IsLocallyConstant.iff_continuous (f : T.unop.left → G)).2 f.continuous⟩
    left_inv := fun f => LocallyConstant.ext (fun _ => rfl)
    right_inv := fun f => ContinuousMap.ext (fun _ => rfl) }) ?_
  intro T₁ T₂ f
  ext g
  apply ContinuousMap.ext
  intro x
  rfl

/-- For a discrete group `G`, the locally constant `G`-valued maps on schemes are the
continuous `G`-valued maps. -/
public def locallyConstantMapsIsoContinuousMaps (G : Type (max (u + 1) v)) [Group G]
    [TopologicalSpace G] [DiscreteTopology G] :
    (locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) ≅
      continuousMapPresheaf.{max (u + 1) v, u} G := by
  refine NatIso.ofComponents (fun T => Equiv.toIso {
    toFun := fun (f : LocallyConstant T.unop G) => f.toContinuousMap
    invFun := fun (f : C(T.unop, G)) =>
      ⟨(f : T.unop → G), (IsLocallyConstant.iff_continuous (f : T.unop → G)).2 f.continuous⟩
    left_inv := fun f => LocallyConstant.ext (fun _ => rfl)
    right_inv := fun f => ContinuousMap.ext (fun _ => rfl) }) ?_
  intro T₁ T₂ f
  ext g
  apply ContinuousMap.ext
  intro x
  rfl

/-- Locally constant maps on the schemes over `S`, pulled back along a functor `H` to the
schemes over `S`, are locally constant maps on the underlying schemes. -/
public def relativeLocallyConstantMapsIsoOnScheme {C : Type (u + 1)} [Category.{u} C]
    (S : Scheme.{u}) (H : C ⥤ Over S) (G : Type (max (u + 1) v)) [Group G] :
    H.op ⋙ locallyConstantMapsOver G S ⋙ forget GrpCat ≅
      (H ⋙ Over.forget S).op ⋙ locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat := by
  refine NatIso.ofComponents (fun T => Iso.refl _) ?_
  intro T₁ T₂ f
  ext g
  rfl

/-- Locally constant `G`-valued maps form a Zariski sheaf on schemes. -/
public theorem locallyConstantMaps_isSheaf_zariski (G : Type (max (u + 1) v)) [Group G] :
    Presheaf.IsSheaf Scheme.zariskiTopology
      (locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) := by
  let : TopologicalSpace G := ⊥
  let : DiscreteTopology G := ⟨rfl⟩
  exact (Presheaf.isSheaf_of_iso_iff (locallyConstantMapsIsoContinuousMaps G)).mpr
    (isSheaf_zariskiTopology_continuousMapPresheaf.{max (u + 1) v, u} G)

/-- Locally constant `G`-valued maps form an fpqc sheaf on the schemes over `S`. -/
public theorem locallyConstantMapsOver_isSheaf_fpqc (S : Scheme.{u})
    (G : Type (max (u + 1) v)) [Group G] :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S)
      (locallyConstantMapsOver G S ⋙ forget GrpCat) := by
  let : TopologicalSpace G := ⊥
  let : DiscreteTopology G := ⟨rfl⟩
  have hG : Presheaf.IsSheaf Scheme.fpqcTopology (continuousMapPresheaf G) :=
    isSheaf_fpqcTopology_continuousMapPresheaf G
  have hS : Presheaf.IsSheaf (Scheme.fpqcTopology.over S)
      ((Over.forget S).op ⋙ continuousMapPresheaf G) :=
    Functor.op_comp_isSheaf_of_isSheaf (Over.forget S) _ Scheme.fpqcTopology _ hG
  exact (Presheaf.isSheaf_of_iso_iff (locallyConstantMapsOverIsoContinuousMaps S G)).mpr hS

/-! ### The constant sheaf on the schemes over a base -/

/-- Sections of a constant presheaf with the same image agree locally, as soon as they agree
over every object with a point and the empty sieve covers every object without points. -/
private theorem isLocallyInjective_of_const {C : Type*} [Category C] {G : Type w}
    {P : Cᵒᵖ ⥤ Type w} (α : (Functor.const Cᵒᵖ).obj G ⟶ P) (J : GrothendieckTopology C)
    (X : C → Type*)
    (hinj : ∀ {T : C} (a b : G), α.app (.op T) a = α.app (.op T) b → Nonempty (X T) → a = b)
    (hBot : ∀ {T : C}, IsEmpty (X T) → (⊥ : Sieve T) ∈ J T) :
    Presheaf.IsLocallyInjective J α := by
  refine ⟨fun {T} a b hab => ?_⟩
  by_cases hab' : a = b
  · subst b
    simp
  · have heq : Presheaf.equalizerSieve
        (F := (Functor.const Cᵒᵖ).obj G) (X := T) a b = ⊥ := by
      ext V f
      simp only [Presheaf.equalizerSieve_apply, Sieve.bot_apply]
      exact ⟨fun hf => hab' (by simpa using hf), False.elim⟩
    rw [heq]
    exact hBot (not_nonempty_iff.mp fun h => hab' (hinj a b hab h))

/-- A map from a constant presheaf to locally constant maps along `F` is locally surjective, as
soon as every open cover of `F.obj T` is refined by a covering family of `T`. -/
private theorem isLocallySurjective_of_open_covers {C : Type*} [Category C]
    (F : C ⥤ Scheme.{u}) (G : Type (max (u + 1) v)) [Group G]
    (α : (Functor.const Cᵒᵖ).obj G ⟶
      (F.op ⋙ locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat))
    (hα : ∀ (T : Cᵒᵖ) (g : G), α.app T g = LocallyConstant.const (F.obj T.unop) g)
    (J : GrothendieckTopology C)
    (hOpen : ∀ {T : C} (U : F.obj T → (F.obj T).Opens),
      TopologicalSpace.IsOpenCover U →
      ∃ (I : Type*) (W : I → C) (a : ∀ i, W i ⟶ T) (r : I → F.obj T),
        Sieve.ofArrows W a ∈ J T ∧ ∀ i y, F.map (a i) y ∈ U (r i)) :
    Presheaf.IsLocallySurjective J α := by
  refine ⟨fun {T} s => ?_⟩
  let s₀ : LocallyConstant (F.obj T) G := s
  choose U hU hx hconst using fun x => s₀.isLocallyConstant.exists_open x
  let V : F.obj T → (F.obj T).Opens := fun x => ⟨U x, hU x⟩
  have hV : TopologicalSpace.IsOpenCover V := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    exact fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  obtain ⟨I, W, a, r, hcover, hmaps⟩ := hOpen V hV
  have hle : Sieve.ofArrows W a ≤ Presheaf.imageSieve α s := by
    intro Y f hf
    obtain ⟨x, g, rfl⟩ := (Sieve.mem_ofArrows_iff W a f).mp hf
    apply (Presheaf.imageSieve α s).downward_closed
    · refine ⟨s₀ (r x), ?_⟩
      rw [hα]
      change LocallyConstant.const (F.obj (W x)) (s₀ (r x)) =
        LocallyConstant.comapMonoidHom (F.map (a x)).base.hom s₀
      ext y
      change s₀ (r x) = s₀ (F.map (a x) y)
      exact (hconst (r x) (F.map (a x) y) (hmaps x y)).symm
  exact J.superset_covering hle hcover

/-- Evaluating the lift of `α` to a sheaf along the sheafification unit recovers `α`. -/
private theorem sheafifyLift_app_toSheafify_app {C : Type*} [Category C]
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type w)] {P Q : Cᵒᵖ ⥤ Type w}
    (α : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) (T : Cᵒᵖ) (g : P.obj T) :
    (sheafifyLift J α hQ).app T ((toSheafify J P).app T g) = α.app T g :=
  congrArg (fun f => f.app T g) (toSheafify_sheafifyLift J α hQ)

/-- Two sections of the constant presheaf on the schemes over `S` with the same constant map
agree locally for every topology finer than the Zariski topology. -/
public theorem constantToLocallyConstantMapsOver_isLocallyInjective (S : Scheme.{u})
    (G : Type (max (u + 1) v)) [Group G] (J : GrothendieckTopology (Over S))
    (hZ : Scheme.zariskiTopology.over S ≤ J) :
    Presheaf.IsLocallyInjective J (constantToLocallyConstantMapsOver S G) := by
  refine isLocallyInjective_of_const _ J (fun T : Over S => T.left) ?_ ?_
  · rintro T a b hab ⟨x⟩
    change LocallyConstant.const T.left a = LocallyConstant.const T.left b at hab
    simpa using congrArg (fun f : LocallyConstant T.left G => f x) hab
  · intro T _
    have hbotBase : (⊥ : Sieve T.left) ∈ Scheme.zariskiTopology T.left :=
      Scheme.bot_mem_grothendieckTopology (P := @IsOpenImmersion) _
    have hbot : (⊥ : Sieve T) ∈ Scheme.zariskiTopology.over S T := by
      simpa using GrothendieckTopology.overEquiv_symm_mem_over Scheme.zariskiTopology T ⊥
        hbotBase
    exact hZ _ hbot

/-- Every locally constant map on an object of the schemes over `S` is locally in the image of
the constant presheaf, for every topology finer than the Zariski topology. -/
public theorem constantToLocallyConstantMapsOver_isLocallySurjective (S : Scheme.{u})
    (G : Type (max (u + 1) v)) [Group G] (J : GrothendieckTopology (Over S))
    (hZ : Scheme.zariskiTopology.over S ≤ J) :
    Presheaf.IsLocallySurjective J (constantToLocallyConstantMapsOver S G) := by
  refine isLocallySurjective_of_open_covers (Over.forget S) G _ (fun _ _ => rfl) J ?_
  intro T U hU
  let 𝒰 := T.left.openCoverOfIsOpenCover U hU
  have hcoverZ : Sieve.ofArrows (fun x => Over.mk (𝒰.f x ≫ T.hom))
      (fun x => Over.homMk (𝒰.f x) (by simp)) ∈ Scheme.zariskiTopology.over S T := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    change Sieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.zariskiTopology T.left
    exact 𝒰.mem_grothendieckTopology
  exact ⟨_, _, _, id, hZ _ hcoverZ, fun i y => y.property⟩

/-- Sheafifying the canonical map from the constant presheaf to the locally constant maps on
the schemes over `S` gives an isomorphism, for every topology finer than the Zariski
topology. -/
public theorem constantToLocallyConstantMapsOver_sheafification_isIso (S : Scheme.{u})
    (G : Type (max (u + 1) v)) [Group G] (J : GrothendieckTopology (Over S))
    (hZ : Scheme.zariskiTopology.over S ≤ J)
    [HasWeakSheafify J (Type (max (u + 1) v))] :
    IsIso ((presheafToSheaf J (Type (max (u + 1) v))).map
      (constantToLocallyConstantMapsOver S G)) := by
  rw [← J.W_iff]
  have : Presheaf.IsLocallyInjective J (constantToLocallyConstantMapsOver S G) :=
    constantToLocallyConstantMapsOver_isLocallyInjective S G J hZ
  have : Presheaf.IsLocallySurjective J (constantToLocallyConstantMapsOver S G) :=
    constantToLocallyConstantMapsOver_isLocallySurjective S G J hZ
  have : J.WEqualsLocallyBijective (Type (max (u + 1) v)) := wEqualsLocallyBijective_type J
  exact (J.W_iff_isLocallyBijective
    (A := Type (max (u + 1) v)) (constantToLocallyConstantMapsOver S G)).mpr
      ⟨inferInstance, inferInstance⟩

/-- The canonical map from the sheafification of a presheaf for one topology to its
sheafification for a finer topology. -/
public def zariskiSheafToTauSheaf {C : Type*} [Category C] (JZ J : GrothendieckTopology C)
    [HasWeakSheafify JZ (Type w)] [HasWeakSheafify J (Type w)] (h : JZ ≤ J)
    (P : Cᵒᵖ ⥤ Type w) :
    sheafify JZ P ⟶ sheafify J P :=
  sheafifyLift JZ (toSheafify J P) (((presheafToSheaf J (Type w)).obj P).property.of_le h)

/-- The identification of the constant sheaf with the locally constant maps, for an arbitrary
chosen sheafification functor on the schemes over `S`. -/
public def constantSheafIsoLocallyConstantMapsOfSheafification (S : Scheme.{u})
    (G : Type (max (u + 1) v)) [Group G] (J : GrothendieckTopology (Over S))
    (hZ : Scheme.zariskiTopology.over S ≤ J) (hF : J ≤ Scheme.fpqcTopology.over S)
    [HasWeakSheafify J (Type (max (u + 1) v))] :
    ((constantSheaf J (Type (max (u + 1) v))).obj G).obj ≅
      (locallyConstantMapsOver G S ⋙ forget GrpCat) := by
  let P := locallyConstantMapsOver G S ⋙ forget GrpCat
  let L : Sheaf J (Type (max (u + 1) v)) :=
    ⟨P, (locallyConstantMapsOver_isSheaf_fpqc S G).of_le hF⟩
  letI : IsIso ((presheafToSheaf J (Type (max (u + 1) v))).map
      (constantToLocallyConstantMapsOver S G)) :=
    constantToLocallyConstantMapsOver_sheafification_isIso S G J hZ
  let e₁ : (constantSheaf J (Type (max (u + 1) v))).obj G ≅
      (presheafToSheaf J (Type (max (u + 1) v))).obj
        (Functor.const (Over S)ᵒᵖ |>.obj G) := Iso.refl _
  let e₂ : (presheafToSheaf J (Type (max (u + 1) v))).obj
      (Functor.const (Over S)ᵒᵖ |>.obj G) ≅
      (presheafToSheaf J (Type (max (u + 1) v))).obj P :=
    asIso ((presheafToSheaf J (Type (max (u + 1) v))).map
      (constantToLocallyConstantMapsOver S G))
  let e₃ : (presheafToSheaf J (Type (max (u + 1) v))).obj P ≅ L :=
    asIso ((sheafificationAdjunction J (Type (max (u + 1) v))).counit.app L)
  simpa [P, L] using (Functor.mapIso (sheafToPresheaf J (Type (max (u + 1) v)))
    ((e₁.trans e₂).trans e₃))

/-- The sheafification of the constant presheaf on the schemes over `S` has the locally
constant `G`-valued maps as its sections, for every topology between the Zariski and the fpqc
topology. -/
@[stacks 03P5]
public def constantSheafIsoLocallyConstantMaps (S : Scheme.{u}) (G : Type (max (u + 1) v))
    [Small.{u} G] [Group G] (J : GrothendieckTopology (Over S))
    (hZ : Scheme.zariskiTopology.over S ≤ J) (hF : J ≤ Scheme.fpqcTopology.over S) :
    ((constantSheaf J (Type (max (u + 1) v))).obj G).obj ≅
      (locallyConstantMapsOver G S ⋙ forget GrpCat) :=
  have : HasWeakSheafify J (Type (max (u + 1) v)) := inferInstance
  constantSheafIsoLocallyConstantMapsOfSheafification S G J hZ hF

/-- The identification of the constant sheaf with locally constant maps sends the
sheafification-unit image of `g` to the constant map with value `g`. -/
@[stacks 03P5 "compatibility with constant sections"]
public theorem constantSheafIsoLocallyConstantMaps_unit (S : Scheme.{u})
    (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] (J : GrothendieckTopology (Over S))
    (hZ : Scheme.zariskiTopology.over S ≤ J) (hF : J ≤ Scheme.fpqcTopology.over S)
    (T : (Over S)ᵒᵖ) (g : G) :
    ((constantSheafIsoLocallyConstantMaps S G J hZ hF).hom.app T)
      ((toSheafify J ((Functor.const (Over S)ᵒᵖ).obj G)).app T g) =
      LocallyConstant.const T.unop.left g := by
  let P := locallyConstantMapsOver G S ⋙ forget GrpCat
  let α := constantToLocallyConstantMapsOver S G
  have hP : Presheaf.IsSheaf J P := (locallyConstantMapsOver_isSheaf_fpqc S G).of_le hF
  change (sheafifyLift J α hP).app T
      ((toSheafify J ((Functor.const (Over S)ᵒᵖ).obj G)).app T g) = _
  exact sheafifyLift_app_toSheafify_app J α hP T g

/-- On the schemes over `S`, the canonical comparison from the Zariski sheafification of the
constant presheaf to its `J`-sheafification is invertible. -/
@[stacks 03P5 "canonical Zariski-to-tau sheafification comparison"]
public theorem constantSheafComparison_isIso (S : Scheme.{u}) (G : Type (max (u + 1) v))
    [Small.{u} G] [Group G] (J : GrothendieckTopology (Over S))
    (hZ : Scheme.zariskiTopology.over S ≤ J) (hF : J ≤ Scheme.fpqcTopology.over S)
    [HasWeakSheafify (Scheme.zariskiTopology.over S) (Type (max (u + 1) v))]
    [HasWeakSheafify J (Type (max (u + 1) v))] :
    let P : (Over S)ᵒᵖ ⥤ Type (max (u + 1) v) := (Functor.const (Over S)ᵒᵖ).obj G
    IsIso (zariskiSheafToTauSheaf (Scheme.zariskiTopology.over S) J hZ P) := by
  let JZ := Scheme.zariskiTopology.over S
  let P := (Functor.const (Over S)ᵒᵖ).obj G
  let hFZ : JZ ≤ Scheme.fpqcTopology.over S := le_trans hZ hF
  let eZ : sheafify JZ P ≅ (locallyConstantMapsOver G S ⋙ forget GrpCat) :=
    constantSheafIsoLocallyConstantMaps S G JZ le_rfl hFZ
  let eJ : sheafify J P ≅ (locallyConstantMapsOver G S ⋙ forget GrpCat) :=
    constantSheafIsoLocallyConstantMaps S G J hZ hF
  let c := zariskiSheafToTauSheaf JZ J hZ P
  have htarget : Presheaf.IsSheaf JZ (locallyConstantMapsOver G S ⋙ forget GrpCat) :=
    (locallyConstantMapsOver_isSheaf_fpqc S G).of_le hFZ
  have hcomp : c ≫ eJ.hom = eZ.hom := by
    apply sheafify_hom_ext JZ (c ≫ eJ.hom) eZ.hom htarget
    ext T g
    change (((toSheafify JZ P ≫ c) ≫ eJ.hom).app T) g =
      (eZ.hom.app T) ((toSheafify JZ P).app T g)
    dsimp [c, zariskiSheafToTauSheaf]
    have hηT' := sheafifyLift_app_toSheafify_app JZ (toSheafify J P)
      (((presheafToSheaf J (Type (max (u + 1) v))).obj P).property.of_le hZ) T g
    rw [hηT']
    change ((constantSheafIsoLocallyConstantMaps S G J hZ hF).hom.app T)
        ((toSheafify J P).app T g) =
      ((constantSheafIsoLocallyConstantMaps S G JZ le_rfl hFZ).hom.app T)
        ((toSheafify JZ P).app T g)
    rw [constantSheafIsoLocallyConstantMaps_unit S G J hZ hF T g,
      constantSheafIsoLocallyConstantMaps_unit S G JZ le_rfl hFZ T g]
  have hc : c = eZ.hom ≫ eJ.inv := eJ.eq_comp_inv.mpr hcomp
  change IsIso c
  rw [hc]
  infer_instance

/-- The constant sheaf of sets is naturally the underlying functor of points of the constant
group scheme. The isomorphism is the composite through the group-valued functor of locally
constant maps. -/
@[stacks 03P5 "representation of the constant sheaf by the group scheme"]
public def constantSheafIsoConstantGroupSchemePoints (S : Scheme.{u})
    (G : Type (max (u + 1) v)) [Small.{u} G] [Group G] (J : GrothendieckTopology (Over S))
    (hZ : Scheme.zariskiTopology.over S ≤ J) (hF : J ≤ Scheme.fpqcTopology.over S) :
    ((constantSheaf J (Type (max (u + 1) v))).obj G).obj ≅
      ((yonedaGrp.obj (constantGroupScheme G S) ⋙
        GrpCat.uliftFunctor.{max (u + 1) v}) ⋙ forget GrpCat) :=
  (constantSheafIsoLocallyConstantMaps S G J hZ hF).trans
    (Functor.isoWhiskerRight (constantGroupSchemePointsIsoLocallyConstantMaps G S).symm
      (forget GrpCat))

/-! ### The constant sheaf along a functor to schemes -/

/-- An identification of a constant sheaf with locally constant maps is compatible with the
sheafification unit if it sends each constant presheaf section to the corresponding constant
map. -/
public def ConstantSheafIso.UnitCompatible {C : Type (u + 1)} [Category.{u} C]
    (F : C ⥤ Scheme.{u}) (J : GrothendieckTopology C) (G : Type (max (u + 1) v)) [Group G]
    (e : ((constantSheaf J (Type (max (u + 1) v))).obj G).obj ≅
      (F.op ⋙ locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat)) : Prop :=
  ∀ (T : Cᵒᵖ) (g : G),
    (e.hom.app T) ((toSheafify J ((Functor.const Cᵒᵖ).obj G)).app T g) =
      LocallyConstant.const (F.obj T.unop) g

/-- The map sending `g : G` to the constant map with value `g`, from the constant presheaf on a
site `C` to the locally constant `G`-valued maps on the schemes `F.obj T`. -/
public def constantToLocallyConstantMapsOn {C : Type (u + 1)} [Category.{u} C]
    (F : C ⥤ Scheme.{u}) (G : Type (max (u + 1) v)) [Group G] :
    (Functor.const Cᵒᵖ).obj G ⟶
      (F.op ⋙ locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) where
  app T := ↾(fun g => LocallyConstant.const (F.obj T.unop) g)
  naturality X Y f := by
    ext g
    rfl

/-- Two sections of the constant presheaf on `C` with the same constant map agree locally, as
soon as the empty sieve covers every object with empty underlying scheme. -/
public theorem constantToLocallyConstantMapsOn_isLocallyInjective {C : Type (u + 1)}
    [Category.{u} C] (F : C ⥤ Scheme.{u}) (G : Type (max (u + 1) v)) [Group G]
    (J : GrothendieckTopology C)
    (hBot : ∀ {T : C}, IsEmpty (F.obj T) → (⊥ : Sieve T) ∈ J T) :
    Presheaf.IsLocallyInjective J (constantToLocallyConstantMapsOn F G) := by
  refine isLocallyInjective_of_const _ J (fun T => F.obj T) ?_ hBot
  rintro T a b hab ⟨x⟩
  change LocallyConstant.const (F.obj T) a = LocallyConstant.const (F.obj T) b at hab
  simpa using congrArg (fun f : LocallyConstant (F.obj T) G => f x) hab

/-- Every locally constant map on `F.obj T` is locally in the image of the constant presheaf,
as soon as every open cover of `F.obj T` is refined by a `J`-covering family of `T`. -/
public theorem constantToLocallyConstantMapsOn_isLocallySurjective {C : Type (u + 1)}
    [Category.{u} C] (F : C ⥤ Scheme.{u}) (G : Type (max (u + 1) v)) [Group G]
    (J : GrothendieckTopology C)
    (hOpen : ∀ {T : C} (U : F.obj T → (F.obj T).Opens),
      TopologicalSpace.IsOpenCover U →
      ∃ (I : Type (u + 1)) (W : I → C) (a : ∀ i, W i ⟶ T) (r : I → F.obj T),
        Sieve.ofArrows W a ∈ J T ∧ ∀ i y, F.map (a i) y ∈ U (r i)) :
    Presheaf.IsLocallySurjective J (constantToLocallyConstantMapsOn F G) :=
  isLocallySurjective_of_open_covers F G _ (fun _ _ => rfl) J hOpen

/-- The constant `J`-sheaf on a site `C` with a functor `F` to schemes is the presheaf of
locally constant maps on the schemes `F.obj T`, as soon as every open cover of `F.obj T` is
refined by a `J`-covering family and that presheaf is a `J`-sheaf. -/
public def constantSheafIsoLocallyConstantMapsOn {C : Type (u + 1)} [Category.{u} C]
    (F : C ⥤ Scheme.{u}) (G : Type (max (u + 1) v)) [Group G] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type (max (u + 1) v))]
    (hOpen : ∀ {T : C} (U : F.obj T → (F.obj T).Opens),
      TopologicalSpace.IsOpenCover U →
      ∃ (I : Type (u + 1)) (W : I → C) (a : ∀ i, W i ⟶ T) (r : I → F.obj T),
        Sieve.ofArrows W a ∈ J T ∧ ∀ i y, F.map (a i) y ∈ U (r i))
    (hEmpty : ∀ {T : C}, IsEmpty (F.obj T) → (⊥ : Sieve T) ∈ J T)
    (hF : Presheaf.IsSheaf J
      (F.op ⋙ locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat)) :
    ((constantSheaf J (Type (max (u + 1) v))).obj G).obj ≅
      (F.op ⋙ locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) := by
  let α := constantToLocallyConstantMapsOn F G
  letI : Presheaf.IsLocallyInjective J α :=
    constantToLocallyConstantMapsOn_isLocallyInjective F G J hEmpty
  letI : Presheaf.IsLocallySurjective J α :=
    constantToLocallyConstantMapsOn_isLocallySurjective F G J hOpen
  letI : J.WEqualsLocallyBijective (Type (max (u + 1) v)) := wEqualsLocallyBijective_type J
  have hα : IsIso ((presheafToSheaf J (Type (max (u + 1) v))).map α) := by
    rw [← J.W_iff]
    exact (J.W_iff_isLocallyBijective α).mpr ⟨inferInstance, inferInstance⟩
  let L : Sheaf J (Type (max (u + 1) v)) := ⟨_, hF⟩
  let e₁ : (constantSheaf J (Type (max (u + 1) v))).obj G ≅
      (presheafToSheaf J (Type (max (u + 1) v))).obj
        ((Functor.const Cᵒᵖ).obj G) := Iso.refl _
  let e₂ : (presheafToSheaf J (Type (max (u + 1) v))).obj ((Functor.const Cᵒᵖ).obj G) ≅
      (presheafToSheaf J (Type (max (u + 1) v))).obj
        (F.op ⋙ locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) :=
    asIso ((presheafToSheaf J (Type (max (u + 1) v))).map α)
  let e₃ : (presheafToSheaf J (Type (max (u + 1) v))).obj
      (F.op ⋙ locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) ≅ L :=
    asIso ((sheafificationAdjunction J (Type (max (u + 1) v))).counit.app L)
  simpa [L, α] using (Functor.mapIso (sheafToPresheaf J (Type (max (u + 1) v)))
    ((e₁.trans e₂).trans e₃))

/-- The identification of the constant sheaf along `F` with locally constant maps is
compatible with the sheafification unit. -/
public theorem constantSheafIsoLocallyConstantMapsOn_unit {C : Type (u + 1)} [Category.{u} C]
    (F : C ⥤ Scheme.{u}) (G : Type (max (u + 1) v)) [Group G] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type (max (u + 1) v))]
    (hOpen : ∀ {T : C} (U : F.obj T → (F.obj T).Opens),
      TopologicalSpace.IsOpenCover U →
      ∃ (I : Type (u + 1)) (W : I → C) (a : ∀ i, W i ⟶ T) (r : I → F.obj T),
        Sieve.ofArrows W a ∈ J T ∧ ∀ i y, F.map (a i) y ∈ U (r i))
    (hEmpty : ∀ {T : C}, IsEmpty (F.obj T) → (⊥ : Sieve T) ∈ J T)
    (hF : Presheaf.IsSheaf J
      (F.op ⋙ locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat)) :
    ConstantSheafIso.UnitCompatible F J G
      (constantSheafIsoLocallyConstantMapsOn F G J hOpen hEmpty hF) := by
  intro T g
  let α := constantToLocallyConstantMapsOn F G
  change (sheafifyLift J α hF).app T
      ((toSheafify J ((Functor.const Cᵒᵖ).obj G)).app T g) = _
  exact sheafifyLift_app_toSheafify_app J α hF T g

/-- If every open cover of `F.obj T` is refined by a `J`-covering family, then the empty sieve
covers every object with empty underlying scheme. -/
public theorem openCoverData_bottom {C : Type (u + 1)} [Category.{u} C] (F : C ⥤ Scheme.{u})
    (J : GrothendieckTopology C)
    (hOpen : ∀ {T : C} (U : F.obj T → (F.obj T).Opens),
      TopologicalSpace.IsOpenCover U →
      ∃ (I : Type (u + 1)) (W : I → C) (a : ∀ i, W i ⟶ T) (r : I → F.obj T),
        Sieve.ofArrows W a ∈ J T ∧ ∀ i y, F.map (a i) y ∈ U (r i)) :
    ∀ {T : C}, IsEmpty (F.obj T) → (⊥ : Sieve T) ∈ J T := by
  intro T hEmpty
  let U : F.obj T → (F.obj T).Opens := fun _ => ⊥
  have hU : TopologicalSpace.IsOpenCover U := by
    rw [TopologicalSpace.IsOpenCover]
    apply le_antisymm
    · exact le_top
    · intro x _
      exact False.elim (hEmpty.false x)
  obtain ⟨I, W, a, r, hcover, _⟩ := hOpen U hU
  have hI : IsEmpty I := ⟨fun i => hEmpty.false (r i)⟩
  have hbot : Sieve.ofArrows W a = (⊥ : Sieve T) := by
    ext Y f
    simp only [Sieve.bot_apply]
    constructor
    · intro hf
      obtain ⟨i, g, rfl⟩ := (Sieve.mem_ofArrows_iff W a f).mp hf
      exact hI.false i
    · intro hf
      exact False.elim hf
  rw [← hbot]
  exact hcover

/-! ### The Zariski topology restricted along a functor to schemes -/

/-- Locally constant maps along `F` form a sheaf for the Zariski topology restricted along
`F`, as soon as `F` creates and preserves pullbacks. -/
public theorem locallyConstantMaps_isSheaf_restrictedZariski {C : Type (u + 1)}
    [Category.{u} C] (F : C ⥤ Scheme.{u})
    (hPres : Limits.PreservesLimitsOfShape Limits.WalkingCospan F)
    [CreatesLimitsOfShape Limits.WalkingCospan F] (G : Type (max (u + 1) v)) [Group G] :
    Presheaf.IsSheaf (F.restrictedTopology Scheme.zariskiTopology)
      (F.op ⋙ locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) := by
  let Q := Scheme.zariskiTopology.toPrecoverage.comap F
  let K := Scheme.zariskiTopology.toPrecoverage.toGrothendieck
  let := hPres
  let : Q.IsStableUnderBaseChange := by dsimp [Q]; infer_instance
  let : Q.HasPullbacks := by dsimp [Q]; infer_instance
  let : Q.PullbacksPreservedBy F := by dsimp [Q]; infer_instance
  let : F.IsContinuous Q.toGrothendieck K :=
    Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy F Q
      Scheme.zariskiTopology.toPrecoverage le_rfl
  have hG : Presheaf.IsSheaf K
      (locallyConstantMaps.{u, max (u + 1) v} G ⋙ forget GrpCat) :=
    Presheaf.IsSheaf.of_le
      (GrothendieckTopology.toGrothendieck_toPrecoverage_le Scheme.zariskiTopology)
      (locallyConstantMaps_isSheaf_zariski G)
  simpa [Functor.restrictedTopology, Q, K] using
    F.op_comp_isSheaf_of_isSheaf Q.toGrothendieck K _ hG

end AlgebraicGeometry

end
