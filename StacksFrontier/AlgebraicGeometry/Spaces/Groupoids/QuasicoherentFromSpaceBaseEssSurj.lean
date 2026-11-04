module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.SingleMorphismHomDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentFromSpaceBaseKernelPair
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentFromSpaceBaseMemberModule
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentFromSpaceBaseTwistModule
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleMorphism
public import StacksFrontier.CategoryTheory.Adjunction.UnitSectionProjection

/-!
# Essential surjectivity of the functor from the base to the groupoid

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces, let `X` be an algebraic space and let
`φ : U ⟶ X` be a surjective étale morphism with `t ≫ φ = s ≫ φ` and `R = U ×_X U` with `t`, `s`
the two projections. Every quasi-coherent module `(ℱ, α)` on the groupoid is isomorphic to one of
the form `(φ^*ℱ', α)` for a quasi-coherent `𝒪_X`-module `ℱ'`. The module `ℱ'` is obtained from
the module on the site `AlgebraicGeometry.Space.QuasiCoherentDescent.SingleSite` of the charts of
`φ` that `(ℱ, α)` gives, through the equivalence
`AlgebraicGeometry.Space.QuasiCoherentDescent.singleRestrictionEquivalence`.

## Main definitions

* `AlgebraicGeometry.Space.transitionSectHet`: a morphism between the inverse images of two
  different modules along two étale morphisms, read on sections over a chart.
* `AlgebraicGeometry.Space.arrowChartTwist`: the morphism of the site of the charts of `φ`
  determined by a chart of the arrow space.
* `AlgebraicGeometry.Space.essSurjModule`: the `𝒪_X`-module attached to a quasi-coherent module
  on the groupoid.
* `AlgebraicGeometry.Space.essSurjComparison`: the isomorphism of its étale pullback along `φ`
  with the module underlying the given quasi-coherent module.

## Main results

* `AlgebraicGeometry.Space.canonicalComparison_hom_eq_unflatten`: the canonical comparison of two
  inverse images along morphisms with equal composites to the base is the unflattened transport
  along that equality.
* `AlgebraicGeometry.Space.hom_ext_of_transitionSectHet`: a morphism between two inverse images is
  determined by its reading on sections.
* `AlgebraicGeometry.Space.comp_map_eq_map_comp_of_transitionSect`: a morphism of modules which
  intertwines two transition morphisms on sections intertwines them.
* `AlgebraicGeometry.Space.isEtale_target`, `AlgebraicGeometry.Space.isEtale_source`: the two
  projections of a kernel-pair groupoid are étale.
* `AlgebraicGeometry.Space.etaleSect_transitionSect_of_eq_unflatten`: the reading of the canonical
  transition morphism on sections over a chart of the arrow space is a transport of sections.
* `AlgebraicGeometry.Space.legTransition_comp_target_source`: at a pair of morphisms which factor
  through the arrow space, the transition morphism read along the pair is `α` reindexed along the
  factorization.
* `AlgebraicGeometry.Space.memberSectMap_arrowChartTwist`: the restriction map of the module that
  `(ℱ, α)` gives, along the twist morphism of a chart `W` of the arrow space, is the reading of
  `α` on sections over `W`.
* `AlgebraicGeometry.Space.exists_spaceBaseObj_iso`: every quasi-coherent module on the groupoid
  is isomorphic to one of the form `(φ^*ℱ', α)`.

## Implementation notes

`AlgebraicGeometry.Space.transitionSect` at the concrete canonical transition morphism makes the
elaborator unfold that morphism, and the reduction does not terminate; so
`AlgebraicGeometry.Space.etaleSect_transitionSect_of_eq_unflatten` is stated at a variable `ψ`
with an equation pinning it down, which is used only after `transitionSect` has been removed.

The equation `spaceBaseDescent … = (canonicalComparison … ).hom` with both sides written out is a
kernel timeout. The single delta steps (`AlgebraicGeometry.Space.modulePullbackUnflatten_eq`,
`AlgebraicGeometry.Space.spaceBaseDescent_eq_unflatten`, `CategoryTheory.iso_trans₃_hom`) are
stated separately and composed with `Eq.trans`.

The underlying module of the attached quasi-coherent module is written
`(spaceBaseObj … ).F.obj` throughout, never as the inverse image along `φ`: crossing between the
two definitionally equal spellings under `CategoryTheory.Functor.map` of
`AlgebraicGeometry.Space.modulePullback` makes the elaborator unfold that functor without coming
back.

## References

* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 041E](https://stacks.math.columbia.edu/tag/041E)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory

universe v₁ u₁

/-- The underlying morphism of a composite of three isomorphisms is the composite of the three
underlying morphisms. -/
theorem iso_trans₃_hom {C : Type u₁} [Category.{v₁} C] {W X Y Z : C} (α : W ≅ X) (β : X ≅ Y)
    (γ : Y ≅ Z) : (α ≪≫ β ≪≫ γ).hom = α.hom ≫ β.hom ≫ γ.hom :=
  rfl

end CategoryTheory

namespace AlgebraicGeometry.Space

open QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Unflattening and the canonical comparison of Stacks 04W5 -/

/-- `AlgebraicGeometry.Space.modulePullbackUnflatten` is the comparison of Stacks 03LU, the given
morphism and the inverse comparison, composed. -/
theorem modulePullbackUnflatten_eq {X Y Z : AlgebraicSpaces B S hS} (φ : Y ⟶ Z) {a b : X ⟶ Y}
    (M : Modules.{u, u} B S hS Z.1 Z.2)
    (ξ : (modulePullback B S hS (a ≫ φ)).obj M ⟶ (modulePullback B S hS (b ≫ φ)).obj M) :
    modulePullbackUnflatten φ ξ =
      (modulePullbackCompIso B S hS a φ).hom.app M ≫ ξ ≫
        (modulePullbackCompIso B S hS b φ).inv.app M :=
  rfl

section Bridge

variable {X Y Z : AlgebraicSpaces B S hS}

/-- The underlying morphism of the canonical comparison of Stacks 04W5 is that of the composite
of the two comparisons of Stacks 03LU with the transport along `h`. -/
private theorem canonicalComparison_hom_eq_trans (a b : X ⟶ Y) (φ : Y ⟶ Z)
    (h : a ≫ φ = b ≫ φ) (M : Modules.{u, u} B S hS Z.1 Z.2) :
    (QuasiCoherentDescent.canonicalComparison a b φ φ h M).hom =
      ((modulePullbackCompIso B S hS a φ).app M ≪≫
        eqToIso (congrArg (fun q : X ⟶ Z => (modulePullback B S hS q).obj M) h) ≪≫
        ((modulePullbackCompIso B S hS b φ).app M).symm).hom :=
  Stacks.CategoryTheory.proj_congr
    (QuasiCoherentDescent.canonicalComparison_eq a b φ φ h M) Iso.hom

/-- The underlying morphism of the composite of the two comparisons of Stacks 03LU with the
transport along `h` is the unflattened transport. -/
private theorem trans_hom_eq_unflatten (a b : X ⟶ Y) (φ : Y ⟶ Z) (h : a ≫ φ = b ≫ φ)
    (M : Modules.{u, u} B S hS Z.1 Z.2) :
    ((modulePullbackCompIso B S hS a φ).app M ≪≫
        eqToIso (congrArg (fun q : X ⟶ Z => (modulePullback B S hS q).obj M) h) ≪≫
        ((modulePullbackCompIso B S hS b φ).app M).symm).hom =
      modulePullbackUnflatten φ (pullbackTransport M h) := by
  rw [modulePullbackUnflatten_eq, CategoryTheory.iso_trans₃_hom]
  exact comp₃_congr rfl rfl rfl

/-- The canonical comparison of Stacks 04W5 of two inverse images, for two morphisms with equal
composites to the base, is the unflattened transport along that equality. -/
theorem canonicalComparison_hom_eq_unflatten (a b : X ⟶ Y) (φ : Y ⟶ Z) (h : a ≫ φ = b ≫ φ)
    (M : Modules.{u, u} B S hS Z.1 Z.2) :
    (QuasiCoherentDescent.canonicalComparison a b φ φ h M).hom =
      modulePullbackUnflatten φ (pullbackTransport M h) :=
  (canonicalComparison_hom_eq_trans B S hS a b φ h M).trans
    (trans_hom_eq_unflatten B S hS a b φ h M)

end Bridge

/-! ### Morphisms of inverse images along two étale morphisms, read on sections -/

section Abstract

variable {C D U V : AlgebraicSpaces B S hS}

/-- Reading a section of an inverse image is injective. -/
private theorem etaleSect_injective_of_etale (g : D ⟶ C) (hg : IsEtale B S hS g.hom)
    (M : Modules.{u, u} B S hS C.1 C.2) (Y : SmallEtale B S hS D.1)
    {m m' : ((modulePullback B S hS g).obj M).val.obj (.op Y)}
    (h : etaleSect B S hS g hg M Y m = etaleSect B S hS g hg M Y m') : m = m' :=
  ((etaleSectInv_etaleSect B S hS g hg M Y m).symm.trans
      (congrArg (etaleSectInv B S hS g hg M Y) h)).trans
    (etaleSectInv_etaleSect B S hS g hg M Y m')

/-- Reading a section back as a section of an inverse image commutes with the inverse image of a
morphism of modules. -/
private theorem etaleSectInv_map (g : D ⟶ C) (hg : IsEtale B S hS g.hom)
    {M N : Modules.{u, u} B S hS C.1 C.2} (w : M ⟶ N) (Y : SmallEtale B S hS D.1)
    (m : M.val.obj (.op ((smallEtalePostcomp B S hS g hg).obj Y))) :
    ((modulePullback B S hS g).map w).val.app (.op Y) (etaleSectInv B S hS g hg M Y m) =
      etaleSectInv B S hS g hg N Y
        (w.val.app (.op ((smallEtalePostcomp B S hS g hg).obj Y)) m) := by
  refine etaleSect_injective_of_etale B S hS g hg N Y
    ((etaleSect_map B S hS g hg w Y _).trans ?_)
  exact (congrArg _ (etaleSect_etaleSectInv B S hS g hg M Y m)).trans
    (etaleSect_etaleSectInv B S hS g hg N Y _).symm

/-- A morphism between the inverse images of two different modules along two étale morphisms,
read on sections over a chart. -/
def transitionSectHet (F F' : Modules.{u, u} B S hS U.1 U.2) {a b : V ⟶ U}
    (ψ : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F')
    (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom) (Y : SmallEtale B S hS V.1)
    (m : F.val.obj (.op ((smallEtalePostcomp B S hS a ha).obj Y))) :
    F'.val.obj (.op ((smallEtalePostcomp B S hS b hb).obj Y)) :=
  etaleSect B S hS b hb F' Y (ψ.val.app (.op Y) (etaleSectInv B S hS a ha F Y m))

/-- The reading of a morphism of inverse images at a section read through Stacks 03LW is the
reading of the morphism on that section. -/
private theorem transitionSectHet_etaleSect (F F' : Modules.{u, u} B S hS U.1 U.2) {a b : V ⟶ U}
    (ψ : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F')
    (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom) (Y : SmallEtale B S hS V.1)
    (x : ((modulePullback B S hS a).obj F).val.obj (.op Y)) :
    transitionSectHet B S hS F F' ψ ha hb Y (etaleSect B S hS a ha F Y x) =
      etaleSect B S hS b hb F' Y (ψ.val.app (.op Y) x) :=
  congrArg (fun z => etaleSect B S hS b hb F' Y (ψ.val.app (.op Y) z))
    (etaleSectInv_etaleSect B S hS a ha F Y x)

/-- A morphism between two inverse images is determined by its reading on sections over every
chart of the test space. -/
theorem hom_ext_of_transitionSectHet (F F' : Modules.{u, u} B S hS U.1 U.2) {a b : V ⟶ U}
    (ψ ψ' : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F')
    (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom)
    (h : ∀ (Y : SmallEtale B S hS V.1)
        (m : F.val.obj (.op ((smallEtalePostcomp B S hS a ha).obj Y))),
      transitionSectHet B S hS F F' ψ ha hb Y m =
        transitionSectHet B S hS F F' ψ' ha hb Y m) :
    ψ = ψ' := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun Y => ?_)
  ext x
  have hx := (transitionSectHet_etaleSect B S hS F F' ψ ha hb Y.unop x).symm.trans
    ((h Y.unop (etaleSect B S hS a ha F Y.unop x)).trans
      (transitionSectHet_etaleSect B S hS F F' ψ' ha hb Y.unop x))
  exact etaleSect_injective_of_etale B S hS b hb F' Y.unop hx

/-- The reading on sections of a morphism of inverse images followed by the inverse image of a
morphism of modules is the reading of the first factor, carried by the second. -/
theorem transitionSectHet_comp_map (F F' : Modules.{u, u} B S hS U.1 U.2) {a b : V ⟶ U}
    (ψ : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F) (θ : F ⟶ F')
    (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom) (Y : SmallEtale B S hS V.1)
    (m : F.val.obj (.op ((smallEtalePostcomp B S hS a ha).obj Y))) :
    transitionSectHet B S hS F F' (ψ ≫ (modulePullback B S hS b).map θ) ha hb Y m =
      θ.val.app (.op ((smallEtalePostcomp B S hS b hb).obj Y))
        (transitionSect B S hS F ψ ha hb Y m) :=
  etaleSect_map B S hS b hb θ Y (ψ.val.app (.op Y) (etaleSectInv B S hS a ha F Y m))

/-- The reading on sections of the inverse image of a morphism of modules followed by a morphism
of inverse images is the morphism of modules on sections, carried by the reading of the second
factor. -/
theorem transitionSectHet_map_comp (F F' : Modules.{u, u} B S hS U.1 U.2) {a b : V ⟶ U}
    (ψ' : (modulePullback B S hS a).obj F' ⟶ (modulePullback B S hS b).obj F') (θ : F ⟶ F')
    (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom) (Y : SmallEtale B S hS V.1)
    (m : F.val.obj (.op ((smallEtalePostcomp B S hS a ha).obj Y))) :
    transitionSectHet B S hS F F' ((modulePullback B S hS a).map θ ≫ ψ') ha hb Y m =
      transitionSect B S hS F' ψ' ha hb Y
        (θ.val.app (.op ((smallEtalePostcomp B S hS a ha).obj Y)) m) :=
  congrArg (fun y => etaleSect B S hS b hb F' Y (ψ'.val.app (.op Y) y))
    (etaleSectInv_map B S hS a ha θ Y m)

/-- A morphism of modules which intertwines two transition morphisms on sections over every chart
intertwines them. -/
theorem comp_map_eq_map_comp_of_transitionSect (F F' : Modules.{u, u} B S hS U.1 U.2)
    {a b : V ⟶ U} (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom)
    (ψ : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F)
    (ψ' : (modulePullback B S hS a).obj F' ⟶ (modulePullback B S hS b).obj F') (θ : F ⟶ F')
    (h : ∀ (Y : SmallEtale B S hS V.1)
        (m : F.val.obj (.op ((smallEtalePostcomp B S hS a ha).obj Y))),
      θ.val.app (.op ((smallEtalePostcomp B S hS b hb).obj Y))
          (transitionSect B S hS F ψ ha hb Y m) =
        transitionSect B S hS F' ψ' ha hb Y
          (θ.val.app (.op ((smallEtalePostcomp B S hS a ha).obj Y)) m)) :
    ψ ≫ (modulePullback B S hS b).map θ = (modulePullback B S hS a).map θ ≫ ψ' := by
  refine hom_ext_of_transitionSectHet B S hS F F' _ _ ha hb fun Y m => ?_
  rw [transitionSectHet_comp_map, transitionSectHet_map_comp, h Y m]

end Abstract

/-! ### The two projections of a kernel-pair groupoid -/

section KernelPair

variable {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
  {X : AlgebraicSpaces B S hS} (φ : G.objects ⟶ X)

/-- A square of algebraic spaces which is a pullback of presheaves is a pullback of algebraic
spaces. -/
theorem isPullback_target_source
    (hpb : IsPullback G.target.hom G.source.hom φ.hom φ.hom) :
    IsPullback G.target G.source φ φ :=
  IsPullback.of_map_of_faithful (ObjectProperty.ι (IsAlgebraicSpace B S hS)) hpb

/-- The target projection of a kernel-pair groupoid of an étale `φ` is étale. -/
theorem isEtale_target (hφet : IsEtale B S hS φ.hom)
    (hpb : IsPullback G.target.hom G.source.hom φ.hom φ.hom) :
    IsEtale B S hS G.target.hom :=
  isEtale_of_isPullback B S hS G.source G.target φ φ
    (isPullback_target_source B S hS G φ hpb).flip hφet

/-- The source projection of a kernel-pair groupoid of an étale `φ` is étale. -/
theorem isEtale_source (hφet : IsEtale B S hS φ.hom)
    (hpb : IsPullback G.target.hom G.source.hom φ.hom φ.hom) :
    IsEtale B S hS G.source.hom :=
  isEtale_of_isPullback B S hS G.target G.source φ φ
    (isPullback_target_source B S hS G φ hpb) hφet

/-- The target projection of a kernel-pair groupoid of a relatively representable `φ` is
relatively representable. -/
theorem relativelyRepresentable_target (hrep : yoneda.relativelyRepresentable φ.hom)
    (hpb : IsPullback G.target.hom G.source.hom φ.hom φ.hom) :
    yoneda.relativelyRepresentable G.target.hom :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip hrep

/-- The source projection of a kernel-pair groupoid of a relatively representable `φ` is
relatively representable. -/
theorem relativelyRepresentable_source (hrep : yoneda.relativelyRepresentable φ.hom)
    (hpb : IsPullback G.target.hom G.source.hom φ.hom φ.hom) :
    yoneda.relativelyRepresentable G.source.hom :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb hrep

end KernelPair

/-! ### The canonical transition morphism of Stacks 03M3, read on sections -/

section Descent

variable {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
  {X : AlgebraicSpaces B S hS} (φ : G.objects ⟶ X) (hφet : IsEtale B S hS φ.hom)
  (hφ : G.target ≫ φ = G.source ≫ φ)

/-- The reading of the canonical transition morphism on sections over a chart `W` of the arrow
space is the transport of sections of `ℱ` along the equality of the two charts of `X` induced by
`W` along `t ≫ φ` and `s ≫ φ`. -/
theorem etaleSect_transitionSect_of_eq_unflatten
    (ht : IsEtale B S hS G.target.hom) (hs : IsEtale B S hS G.source.hom)
    (htφ : IsEtale B S hS (G.target ≫ φ).hom) (hsφ : IsEtale B S hS (G.source ≫ φ).hom)
    (hct : EtaleRestrictionComp B S hS G.target φ ht hφet htφ)
    (hcs : EtaleRestrictionComp B S hS G.source φ hs hφet hsφ)
    (M : Modules.{u, u} B S hS X.1 X.2)
    (ψ : (modulePullback B S hS G.target).obj ((modulePullback B S hS φ).obj M) ⟶
      (modulePullback B S hS G.source).obj ((modulePullback B S hS φ).obj M))
    (hψ : ψ = modulePullbackUnflatten φ (pullbackTransport M hφ))
    (W : SmallEtale B S hS G.arrows.1)
    (m : ((modulePullback B S hS φ).obj M).val.obj
      (.op ((smallEtalePostcomp B S hS G.target ht).obj W))) :
    etaleSect B S hS φ hφet M ((smallEtalePostcomp B S hS G.source hs).obj W)
        (transitionSect B S hS ((modulePullback B S hS φ).obj M) ψ ht hs W m) =
      eqToHom (congrArg (fun V : SmallEtale B S hS X.1 => M.val.presheaf.obj (.op V))
          (smallEtalePostcomp_obj_congr B S hS htφ hsφ hφ W))
        (etaleSect B S hS φ hφet M ((smallEtalePostcomp B S hS G.target ht).obj W) m) := by
  have hψ' : ψ = (canonicalComparison G.target G.source φ φ hφ M).hom :=
    hψ.trans (canonicalComparison_hom_eq_unflatten B S hS G.target G.source φ hφ M).symm
  refine Eq.trans (congrArg
      (etaleSect B S hS φ hφet M ((smallEtalePostcomp B S hS G.source hs).obj W))
      (transitionSect_eq B S hS ((modulePullback B S hS φ).obj M) ψ ht hs W m)) ?_
  rw [hψ']
  exact (canonicalComparison_etaleSect B S hS G.target G.source φ φ hφ ht hs hφet hφet
      htφ hsφ hct hcs M W
      (etaleSectInv B S hS G.target ht ((modulePullback B S hS φ).obj M) W m)).trans
    (congrArg (fun z =>
        eqToHom (congrArg (fun V : SmallEtale B S hS X.1 => M.val.presheaf.obj (.op V))
            (smallEtalePostcomp_obj_congr B S hS htφ hsφ hφ W))
          (etaleSect B S hS φ hφet M ((smallEtalePostcomp B S hS G.target ht).obj W) z))
      (etaleSect_etaleSectInv B S hS G.target ht ((modulePullback B S hS φ).obj M) W m))

/-- The canonical transition morphism is the unflattened transport along `t ≫ φ = s ≫ φ`. -/
theorem spaceBaseDescent_eq_unflatten (M : Modules.{u, u} B S hS X.1 X.2) :
    spaceBaseDescent B S hS G φ hφ M = modulePullbackUnflatten φ (pullbackTransport M hφ) :=
  rfl

end Descent

/-! ### The transition morphism of the groupoid at the two projections -/

section LegAtProjections

variable {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
  {X : AlgebraicSpaces B S hS} (φ : G.objects ⟶ X)
  (hpb : IsPullback G.target.hom G.source.hom φ.hom φ.hom)
  (Z : QuasicoherentModule B S hS G) {P : AlgebraicSpaces B S hS}

/-- `AlgebraicGeometry.Space.legTransition` is the reindexing of `α` along the lift of the pair
between the two transports along the equations of the lift. -/
private theorem legTransition_eq' (a b : P ⟶ G.objects) (hab : a ≫ φ = b ≫ φ) :
    legTransition B S hS G φ hpb Z a b hab =
      comp₃ (pullbackTransport Z.F.obj (arrowLift_comp_target B S hS G φ hpb a b hab).symm)
        (transitionReindex B S hS Z.F.obj Z.alpha (arrowLift B S hS G φ hpb a b hab))
        (pullbackTransport Z.F.obj (arrowLift_comp_source B S hS G φ hpb a b hab)) :=
  rfl

/-- `AlgebraicGeometry.Space.legSect` is the reading on sections of
`AlgebraicGeometry.Space.legTransition`. -/
private theorem legSect_eq' (a b : P ⟶ G.objects) (ha : IsEtale B S hS a.hom)
    (hb : IsEtale B S hS b.hom) (hab : a ≫ φ = b ≫ φ) (Y : SmallEtale B S hS P.1)
    (m : Z.F.obj.val.obj (.op ((smallEtalePostcomp B S hS a ha).obj Y))) :
    legSect B S hS G φ hpb Z a b ha hb hab Y m =
      transitionSect B S hS Z.F.obj (legTransition B S hS G φ hpb Z a b hab) ha hb Y m :=
  rfl

/-- At a pair of morphisms which factor through the arrow space, the transition morphism read
along the pair is the reindexing of `α` along the factorization. -/
theorem legTransition_comp_target_source (w : P ⟶ G.arrows)
    (hab : (w ≫ G.target) ≫ φ = (w ≫ G.source) ≫ φ) :
    legTransition B S hS G φ hpb Z (w ≫ G.target) (w ≫ G.source) hab =
      transitionReindex B S hS Z.F.obj Z.alpha w := by
  have key : ∀ (v : P ⟶ G.arrows), v = w →
      ∀ (e₁ : w ≫ G.target = v ≫ G.target) (e₂ : v ≫ G.source = w ≫ G.source),
      comp₃ (pullbackTransport Z.F.obj e₁)
          (transitionReindex B S hS Z.F.obj Z.alpha v) (pullbackTransport Z.F.obj e₂) =
        transitionReindex B S hS Z.F.obj Z.alpha w := by
    rintro v rfl e₁ e₂
    obtain rfl : e₁ = rfl := rfl
    obtain rfl : e₂ = rfl := rfl
    simp [comp₃, pullbackTransport]
  rw [legTransition_eq']
  exact key _ (arrowLift_unique B S hS G φ hpb hab w rfl rfl).symm _ _

/-- At a pair of morphisms which factor through the arrow space, the reading of the transition
morphism on sections is the reading of `α` itself, over the chart that the factorization
induces. -/
theorem legSect_comp_target_source (w : P ⟶ G.arrows) (hw : IsEtale B S hS w.hom)
    (ht : IsEtale B S hS G.target.hom) (hs : IsEtale B S hS G.source.hom)
    (hwt : IsEtale B S hS (w ≫ G.target).hom) (hws : IsEtale B S hS (w ≫ G.source).hom)
    (hab : (w ≫ G.target) ≫ φ = (w ≫ G.source) ≫ φ)
    (hct : EtaleRestrictionComp B S hS w G.target hw ht hwt)
    (hcs : EtaleRestrictionComp B S hS w G.source hw hs hws)
    (Y : SmallEtale B S hS P.1)
    (m : Z.F.obj.val.obj (.op ((smallEtalePostcomp B S hS (w ≫ G.target) hwt).obj Y))) :
    legSect B S hS G φ hpb Z (w ≫ G.target) (w ≫ G.source) hwt hws hab Y m =
      transitionSect B S hS Z.F.obj Z.alpha ht hs
        ((smallEtalePostcomp B S hS w hw).obj Y) m := by
  rw [legSect_eq', legTransition_comp_target_source]
  exact transitionSect_transitionReindex B S hS Z.F.obj Z.alpha w hw ht hs hwt hws hct hcs Y m

end LegAtProjections


/-! ### The twist morphism determined by a chart of the arrow space -/

section Twist

variable {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
  {X : AlgebraicSpaces B S hS} (φ : G.objects ⟶ X) (hφet : IsEtale B S hS φ.hom)
  (hφ : G.target ≫ φ = G.source ≫ φ)

/-- The twist morphism determined by a chart `W` of the arrow space: the identity of the scheme
of `W`, as a morphism between the charts of `X` induced by `W` along `s ≫ φ` and along `t ≫ φ`,
that is, a morphism of the site of the charts of `φ`. -/
def arrowChartTwist (ht : IsEtale B S hS G.target.hom) (hs : IsEtale B S hS G.source.hom)
    (W : SmallEtale B S hS G.arrows.1) :
    (smallEtalePostcomp B S hS φ hφet).obj ((smallEtalePostcomp B S hS G.source hs).obj W) ⟶
      (smallEtalePostcomp B S hS φ hφet).obj
        ((smallEtalePostcomp B S hS G.target ht).obj W) :=
  ObjectProperty.homMk (CostructuredArrow.homMk (𝟙 W.1.left) (by
    change yoneda.map (𝟙 W.1.left) ≫ (W.1.hom ≫ G.target.hom) ≫ φ.hom =
      (W.1.hom ≫ G.source.hom) ≫ φ.hom
    rw [yoneda.map_id, Category.id_comp, Category.assoc, Category.assoc]
    exact congrArg (fun z => W.1.hom ≫ z) (congrArg (fun f : G.arrows ⟶ X => f.hom) hφ)))

/-- The twist morphism is the identity on the underlying scheme. -/
theorem arrowChartTwist_hom_left (ht : IsEtale B S hS G.target.hom)
    (hs : IsEtale B S hS G.source.hom) (W : SmallEtale B S hS G.arrows.1) :
    (arrowChartTwist B S hS G φ hφet hφ ht hs W).hom.left = 𝟙 W.1.left :=
  rfl

/-- The twist morphism is the transport along the equality of the two charts of `X` that a chart
of the arrow space induces along the two projections. -/
theorem eqToHom_eq_arrowChartTwist (ht : IsEtale B S hS G.target.hom)
    (hs : IsEtale B S hS G.source.hom)
    (htφ : IsEtale B S hS (G.target ≫ φ).hom) (hsφ : IsEtale B S hS (G.source ≫ φ).hom)
    (W : SmallEtale B S hS G.arrows.1) :
    eqToHom (smallEtalePostcomp_obj_congr B S hS htφ hsφ hφ W).symm =
      arrowChartTwist B S hS G φ hφet hφ ht hs W := by
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  rw [eqToHom_hom_left]
  rfl

/-- The second leg attached to the twist morphism is the structure morphism of the chart of the
arrow space followed by the target projection. -/
theorem chartLegSnd_arrowChartTwist (ht : IsEtale B S hS G.target.hom)
    (hs : IsEtale B S hS G.source.hom) (W : SmallEtale B S hS G.arrows.1) :
    chartLegSnd B S hS φ hφet (arrowChartTwist B S hS G φ hφet hφ ht hs W) =
      chartLegFst B S hS W ≫ G.target := by
  apply ObjectProperty.hom_ext
  show yoneda.map (𝟙 W.1.left) ≫ (W.1.hom ≫ G.target.hom) = W.1.hom ≫ G.target.hom
  rw [yoneda.map_id, Category.id_comp]

end Twist

/-! ### The restriction map of the attached module at a twist morphism -/

section Member

variable {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
  {X : AlgebraicSpaces B S hS} (φ : G.objects ⟶ X) (hφet : IsEtale B S hS φ.hom)

/-- The reading of the transition morphism along a leg, after a restriction map, is unchanged when
the leg is replaced by an equal one and the restriction map by one with the same underlying
scheme map. -/
private theorem legSect_val_map_of_leg_eq
    (hpb : IsPullback G.target.hom G.source.hom φ.hom φ.hom)
    (Z : QuasicoherentModule B S hS G) {P : AlgebraicSpaces B S hS}
    (a a' b : P ⟶ G.objects) (ha : IsEtale B S hS a.hom) (ha' : IsEtale B S hS a'.hom)
    (hb : IsEtale B S hS b.hom) (hab : a ≫ φ = b ≫ φ) (ha'b : a' ≫ φ = b ≫ φ) (e : a' = a)
    (Y : SmallEtale B S hS P.1) {D : SmallEtale B S hS G.objects.1}
    (c₁ : (smallEtalePostcomp B S hS a' ha').obj Y ⟶ D)
    (c₂ : (smallEtalePostcomp B S hS a ha).obj Y ⟶ D) (hc : c₁.hom.left = c₂.hom.left)
    (m : Z.F.obj.val.obj (.op D)) :
    legSect B S hS G φ hpb Z a' b ha' hb ha'b Y (Z.F.obj.val.map c₁.op m) =
      legSect B S hS G φ hpb Z a b ha hb hab Y (Z.F.obj.val.map c₂.op m) := by
  subst e
  obtain rfl : c₁ = c₂ := ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ hc)
  rfl

/-- The restriction map of the module attached to `(ℱ, α)` along the twist morphism of a chart of
the arrow space is the reading of the transition morphism along the two legs of that chart. -/
theorem memberSectMap_arrowChartTwist_eq_legSect
    (hφ : G.target ≫ φ = G.source ≫ φ)
    (hpb : IsPullback G.target.hom G.source.hom φ.hom φ.hom)
    (Z : QuasicoherentModule B S hS G) (ht : IsEtale B S hS G.target.hom)
    (hs : IsEtale B S hS G.source.hom) (W : SmallEtale B S hS G.arrows.1)
    (hwt : IsEtale B S hS (chartLegFst B S hS W ≫ G.target).hom)
    (hws : IsEtale B S hS (chartLegFst B S hS W ≫ G.source).hom)
    (hab : (chartLegFst B S hS W ≫ G.target) ≫ φ = (chartLegFst B S hS W ≫ G.source) ≫ φ)
    (y : Z.F.obj.val.obj (.op ((smallEtalePostcomp B S hS G.target ht).obj W))) :
    memberSectMap B S hS G φ hφet hpb Z
        (singleHom B S hS φ hφet (arrowChartTwist B S hS G φ hφet hφ ht hs W)) y =
      legSect B S hS G φ hpb Z (chartLegFst B S hS W ≫ G.target)
        (chartLegFst B S hS W ≫ G.source) hwt hws hab (chartTestUnit B S hS W) y :=
  (memberSectMap_eq B S hS G φ hφet hpb Z
      (singleHom B S hS φ hφet (arrowChartTwist B S hS G φ hφet hφ ht hs W)) y).trans
    ((legSect_val_map_of_leg_eq B S hS G φ hpb Z (chartLegFst B S hS W ≫ G.target)
        (chartLegSnd B S hS φ hφet (arrowChartTwist B S hS G φ hφet hφ ht hs W))
        (chartLegFst B S hS W ≫ G.source) hwt
        (isEtale_chartLegSnd B S hS φ hφet (arrowChartTwist B S hS G φ hφet hφ ht hs W)) hws
        hab
        (chartLeg_condition B S hS φ hφet
          (arrowChartTwist B S hS G φ hφet hφ ht hs W)).symm
        (chartLegSnd_arrowChartTwist B S hS G φ hφet hφ ht hs W) (chartTestUnit B S hS W)
        (chartUnitSnd B S hS φ hφet (arrowChartTwist B S hS G φ hφet hφ ht hs W))
        (𝟙 ((smallEtalePostcomp B S hS G.target ht).obj W)) rfl y).trans
      (legSect_congr B S hS G φ hpb Z (chartLegFst B S hS W ≫ G.target)
        (chartLegFst B S hS W ≫ G.source) hwt hws hab (chartTestUnit B S hS W)
        (val_map_id B S hS G Z y)))

/-- The restriction map of the module attached to `(ℱ, α)` along the twist morphism of a chart
`W` of the arrow space is the reading of `α` on sections over `W`. -/
theorem memberSectMap_arrowChartTwist (hφ : G.target ≫ φ = G.source ≫ φ)
    (hrep : yoneda.relativelyRepresentable φ.hom)
    (hpb : IsPullback G.target.hom G.source.hom φ.hom φ.hom)
    (Z : QuasicoherentModule B S hS G) (ht : IsEtale B S hS G.target.hom)
    (hs : IsEtale B S hS G.source.hom) (W : SmallEtale B S hS G.arrows.1)
    (y : Z.F.obj.val.obj (.op ((smallEtalePostcomp B S hS G.target ht).obj W))) :
    memberSectMap B S hS G φ hφet hpb Z
        (singleHom B S hS φ hφet (arrowChartTwist B S hS G φ hφet hφ ht hs W)) y =
      transitionSect B S hS Z.F.obj Z.alpha ht hs W y := by
  have hw : IsEtale B S hS (chartLegFst B S hS W).hom := isEtale_chartLegFst B S hS W
  have hwt : IsEtale B S hS (chartLegFst B S hS W ≫ G.target).hom := isEtale_comp B S hS hw ht
  have hws : IsEtale B S hS (chartLegFst B S hS W ≫ G.source).hom := isEtale_comp B S hS hw hs
  have hab : (chartLegFst B S hS W ≫ G.target) ≫ φ =
      (chartLegFst B S hS W ≫ G.source) ≫ φ := by
    rw [Category.assoc, Category.assoc, hφ]
  have hrepw : yoneda.relativelyRepresentable (chartLegFst B S hS W).hom :=
    relativelyRepresentable_of_isAlgebraicSpace B S hS G.arrows.2 (chartLegFst B S hS W).hom
  have hca : EtaleRestrictionComp B S hS (chartLegFst B S hS W) G.target hw ht hwt :=
    etaleRestrictionComp_of_representable B S hS (chartLegFst B S hS W) G.target hw ht hwt
      hrepw (relativelyRepresentable_target B S hS G φ hrep hpb)
      (relativelyRepresentable_of_isAlgebraicSpace B S hS G.objects.2
        (chartLegFst B S hS W ≫ G.target).hom)
  have hcs : EtaleRestrictionComp B S hS (chartLegFst B S hS W) G.source hw hs hws :=
    etaleRestrictionComp_of_representable B S hS (chartLegFst B S hS W) G.source hw hs hws
      hrepw (relativelyRepresentable_source B S hS G φ hrep hpb)
      (relativelyRepresentable_of_isAlgebraicSpace B S hS G.objects.2
        (chartLegFst B S hS W ≫ G.source).hom)
  exact (memberSectMap_arrowChartTwist_eq_legSect B S hS G φ hφet hφ hpb Z ht hs W
      hwt hws hab y).trans
    (legSect_comp_target_source B S hS G φ hpb Z (chartLegFst B S hS W) hw ht hs hwt hws hab
      hca hcs (chartTestUnit B S hS W) y)

end Member

/-! ### Essential surjectivity from a comparison on the charts of `U` -/

section Assembly

variable {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
  {X : AlgebraicSpaces B S hS} (φ : G.objects ⟶ X) (hφet : IsEtale B S hS φ.hom)
  (hφ : G.target ≫ φ = G.source ≫ φ)

/-- An isomorphism of the two underlying modules which is compatible with the two transition
morphisms gives an isomorphism of quasi-coherent modules on the groupoid. -/
theorem nonempty_iso_of_hom_iso {M N : QuasicoherentModule B S hS G} (e : M.F.obj ≅ N.F.obj)
    (hc : QuasicoherentModule.Compatible e.hom) : Nonempty (M ≅ N) := by
  have : IsIso ((QuasicoherentModule.forget G).map (QuasicoherentModule.homMk e.hom hc)) := by
    show IsIso e.hom
    infer_instance
  have := isIso_of_reflects_iso (QuasicoherentModule.homMk e.hom hc)
    (QuasicoherentModule.forget G)
  exact ⟨asIso (QuasicoherentModule.homMk e.hom hc)⟩

/-- The member of a one-member étale covering is surjective. -/
theorem isSurjective_of_isEtaleCovering_single
    (hcov : IsEtaleCovering B S hS (fun _ : Unit => G.objects.1) (fun _ => φ.hom)) :
    IsSurjective B S hS φ.hom := fun x => by
  obtain ⟨_, hx⟩ := Set.mem_iUnion.1 (Set.eq_univ_iff_forall.1 hcov.jointly_surjective x)
  exact hx

/-- An isomorphism `eU` of the étale pullback of `ℱ'` along `φ` with `ℱ` which is compatible with
the twist morphism of every chart of the arrow space is compatible with the two transition
morphisms. -/
theorem compatible_of_twistNaturality
    (hrep : yoneda.relativelyRepresentable φ.hom)
    (hpb : IsPullback G.target.hom G.source.hom φ.hom φ.hom)
    (F : QuasicoherentSheaves.{u, u} B S hS X.obj X.property)
    (Z : QuasicoherentModule B S hS G) (ht : IsEtale B S hS G.target.hom)
    (hs : IsEtale B S hS G.source.hom)
    (eU : (etaleModulePullback.{u, u} B S hS φ hφet).obj F.obj ≅ Z.F.obj)
    (hnat : ∀ (W : SmallEtale B S hS G.arrows.1)
        (n : F.obj.val.obj (.op ((smallEtalePostcomp B S hS φ hφet).obj
          ((smallEtalePostcomp B S hS G.target ht).obj W)))),
      eU.hom.val.app (.op ((smallEtalePostcomp B S hS G.source hs).obj W))
          (F.obj.val.map (arrowChartTwist B S hS G φ hφet hφ ht hs W).op n) =
        transitionSect B S hS Z.F.obj Z.alpha ht hs W
          (eU.hom.val.app (.op ((smallEtalePostcomp B S hS G.target ht).obj W)) n)) :
    QuasicoherentModule.Compatible (M := spaceBaseObj B S hS G φ hφ F) (N := Z)
      (((modulePullbackIsoEtaleModulePullback B S hS φ hφet).app F.obj ≪≫ eU).hom) := by
  have htφ : IsEtale B S hS (G.target ≫ φ).hom := isEtale_comp B S hS ht hφet
  have hsφ : IsEtale B S hS (G.source ≫ φ).hom := isEtale_comp B S hS hs hφet
  have hct : EtaleRestrictionComp B S hS G.target φ ht hφet htφ :=
    etaleRestrictionComp_of_representable B S hS G.target φ ht hφet htφ
      (relativelyRepresentable_target B S hS G φ hrep hpb) hrep
      (MorphismProperty.comp_mem _ _ _
        (relativelyRepresentable_target B S hS G φ hrep hpb) hrep)
  have hcs : EtaleRestrictionComp B S hS G.source φ hs hφet hsφ :=
    etaleRestrictionComp_of_representable B S hS G.source φ hs hφet hsφ
      (relativelyRepresentable_source B S hS G φ hrep hpb) hrep
      (MorphismProperty.comp_mem _ _ _
        (relativelyRepresentable_source B S hS G φ hrep hpb) hrep)
  refine comp_map_eq_map_comp_of_transitionSect B S hS
    (spaceBaseObj B S hS G φ hφ F).F.obj Z.F.obj ht hs
    (spaceBaseObj B S hS G φ hφ F).alpha Z.alpha
    (((modulePullbackIsoEtaleModulePullback B S hS φ hφet).app F.obj ≪≫ eU).hom)
    fun W m => ?_
  have hn := etaleSect_transitionSect_of_eq_unflatten B S hS G φ hφet hφ ht hs htφ hsφ
    hct hcs F.obj (spaceBaseObj B S hS G φ hφ F).alpha
    ((spaceBaseObj_alpha B S hS G φ hφ F).trans
      (spaceBaseDescent_eq_unflatten B S hS G φ hφ F.obj)) W m
  have htr : eqToHom (congrArg
          (fun V : SmallEtale B S hS X.1 => F.obj.val.presheaf.obj (.op V))
          (smallEtalePostcomp_obj_congr B S hS htφ hsφ hφ W))
        (etaleSect B S hS φ hφet F.obj ((smallEtalePostcomp B S hS G.target ht).obj W) m) =
      F.obj.val.map (arrowChartTwist B S hS G φ hφet hφ ht hs W).op
        (etaleSect B S hS φ hφet F.obj
          ((smallEtalePostcomp B S hS G.target ht).obj W) m) := by
    rw [← eqToHom_eq_arrowChartTwist B S hS G φ hφet hφ ht hs htφ hsφ W]
    exact (val_map_eqToHom B S hS (smallEtalePostcomp_obj_congr B S hS htφ hsφ hφ W) F.obj
      (etaleSect B S hS φ hφet F.obj
        ((smallEtalePostcomp B S hS G.target ht).obj W) m)).symm
  exact (congrArg
      (fun z => eU.hom.val.app (.op ((smallEtalePostcomp B S hS G.source hs).obj W)) z)
      (hn.trans htr)).trans
    (hnat W (etaleSect B S hS φ hφet F.obj
      ((smallEtalePostcomp B S hS G.target ht).obj W) m))

/-- The quasi-coherent module on the groupoid attached to `ℱ'` is isomorphic to `(ℱ, α)`, given
an isomorphism `eU` of the étale pullback of `ℱ'` along `φ` with `ℱ` compatible with the twist
morphism of every chart of the arrow space. -/
theorem nonempty_spaceBaseObj_iso_of_etaleComparison
    (hrep : yoneda.relativelyRepresentable φ.hom)
    (hpb : IsPullback G.target.hom G.source.hom φ.hom φ.hom)
    (F : QuasicoherentSheaves.{u, u} B S hS X.obj X.property)
    (Z : QuasicoherentModule B S hS G) (ht : IsEtale B S hS G.target.hom)
    (hs : IsEtale B S hS G.source.hom)
    (eU : (etaleModulePullback.{u, u} B S hS φ hφet).obj F.obj ≅ Z.F.obj)
    (hnat : ∀ (W : SmallEtale B S hS G.arrows.1)
        (n : F.obj.val.obj (.op ((smallEtalePostcomp B S hS φ hφet).obj
          ((smallEtalePostcomp B S hS G.target ht).obj W)))),
      eU.hom.val.app (.op ((smallEtalePostcomp B S hS G.source hs).obj W))
          (F.obj.val.map (arrowChartTwist B S hS G φ hφet hφ ht hs W).op n) =
        transitionSect B S hS Z.F.obj Z.alpha ht hs W
          (eU.hom.val.app (.op ((smallEtalePostcomp B S hS G.target ht).obj W)) n)) :
    Nonempty (spaceBaseObj B S hS G φ hφ F ≅ Z) :=
  nonempty_iso_of_hom_iso B S hS G (M := spaceBaseObj B S hS G φ hφ F) (N := Z)
    ((modulePullbackIsoEtaleModulePullback B S hS φ hφet).app F.obj ≪≫ eU)
    (compatible_of_twistNaturality B S hS G φ hφet hφ hrep hpb F Z ht hs eU hnat)

/-- A quasi-coherent module `(ℱ, α)` on the groupoid is isomorphic to the one attached to a
quasi-coherent `𝒪_X`-module, given an `𝒪_X`-module `M` and an isomorphism of its étale pullback
along `φ` with `ℱ` compatible with the twist morphism of every chart of the arrow space. -/
theorem exists_spaceBaseObj_iso_of_etaleComparison
    (hcov : IsEtaleCovering B S hS (fun _ : Unit => G.objects.1) (fun _ => φ.hom))
    (hrep : yoneda.relativelyRepresentable φ.hom)
    (hpb : IsPullback G.target.hom G.source.hom φ.hom φ.hom)
    (Z : QuasicoherentModule B S hS G) (ht : IsEtale B S hS G.target.hom)
    (hs : IsEtale B S hS G.source.hom) (M : Modules.{u, u} B S hS X.1 X.2)
    (eU : (etaleModulePullback.{u, u} B S hS φ hφet).obj M ≅ Z.F.obj)
    (hnat : ∀ (W : SmallEtale B S hS G.arrows.1)
        (n : M.val.obj (.op ((smallEtalePostcomp B S hS φ hφet).obj
          ((smallEtalePostcomp B S hS G.target ht).obj W)))),
      eU.hom.val.app (.op ((smallEtalePostcomp B S hS G.source hs).obj W))
          (M.val.map (arrowChartTwist B S hS G φ hφet hφ ht hs W).op n) =
        transitionSect B S hS Z.F.obj Z.alpha ht hs W
          (eU.hom.val.app (.op ((smallEtalePostcomp B S hS G.target ht).obj W)) n)) :
    ∃ F : QuasicoherentSheaves.{u, u} B S hS X.obj X.property,
      Nonempty (spaceBaseObj B S hS G φ hφ F ≅ Z) :=
  ⟨⟨M, (isQuasicoherentOnSite_etaleModulePullback_iff B S hS φ hφet
        (isSurjective_of_isEtaleCovering_single B S hS G φ hcov) M).2
      (SheafOfModules.IsQuasicoherentOnSite.of_iso eU.symm Z.F.property)⟩,
    nonempty_spaceBaseObj_iso_of_etaleComparison B S hS G φ hφet hφ hrep hpb _ Z ht hs eU hnat⟩

end Assembly

/-! ### The module produced by the Comparison Lemma -/

section Final

variable {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
  {X : AlgebraicSpaces B S hS} (φ : G.objects ⟶ X) (hφet : IsEtale B S hS φ.hom)
  (hφ : G.target ≫ φ = G.source ≫ φ)
  (hpb : IsPullback G.target.hom G.source.hom φ.hom φ.hom)
  (Z : QuasicoherentModule B S hS G)

section CoverDense

variable [(singleFunctor B S hS φ hφet).IsCoverDense (SmallEtale.topology B S hS X.1)]

/-- The `𝒪_X`-module attached to a quasi-coherent module on the groupoid: the image of the module
on the site of the charts of `φ` that `(ℱ, α)` gives under the inverse of
`AlgebraicGeometry.Space.QuasiCoherentDescent.singleRestrictionEquivalence`. -/
def essSurjModule : Modules.{u, u} B S hS X.1 X.2 :=
  (singleRestrictionEquivalence B S hS φ hφet).inverse.obj
    (memberModule B S hS G φ hφet hpb Z)

/-- The restriction of `AlgebraicGeometry.Space.essSurjModule` to the site of the charts of `φ`
is isomorphic to the module that `(ℱ, α)` gives. -/
def essSurjCounit :
    (singleRestriction B S hS φ hφet).obj (essSurjModule B S hS G φ hφet hpb Z) ≅
      memberModule B S hS G φ hφet hpb Z :=
  (singleRestrictionEquivalence B S hS φ hφet).counitIso.app
    (memberModule B S hS G φ hφet hpb Z)

/-- The isomorphism of the sections over a chart of `U` of the étale pullback of
`AlgebraicGeometry.Space.essSurjModule` with the sections of `ℱ`, given by
`AlgebraicGeometry.Space.essSurjCounit`. -/
def essSurjCompApp (V : (SmallEtale B S hS G.objects.1)ᵒᵖ) :
    ((etaleModulePullback.{u, u} B S hS φ hφet).obj
        (essSurjModule B S hS G φ hφet hpb Z)).val.obj V ≅ Z.F.obj.val.obj V :=
  (SheafOfModules.forget (singleRing B S hS φ hφet) ⋙
      PresheafOfModules.evaluation _ (.op (singleObj B S hS φ hφet V.unop))).mapIso
    (essSurjCounit B S hS G φ hφet hpb Z)

/-- The isomorphism of the étale pullback of `AlgebraicGeometry.Space.essSurjModule` along `φ`
with the module `ℱ` underlying `(ℱ, α)`. -/
def essSurjComparison :
    (etaleModulePullback.{u, u} B S hS φ hφet).obj (essSurjModule B S hS G φ hφet hpb Z) ≅
      Z.F.obj :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (essSurjCompApp B S hS G φ hφet hpb Z) (fun {V V'} f => by
      ext x
      exact (PresheafOfModules.naturality_apply (essSurjCounit B S hS G φ hφet hpb Z).hom.val
        ((singleInclusion B S hS φ hφet).map f.unop).op x).trans
        ((memberModule_val_map B S hS G φ hφet hpb Z
          ((singleInclusion B S hS φ hφet).map f.unop) _).trans
        (memberSectMap_singleInclusion B S hS G φ hφet hpb Z f.unop _))))

/-- `AlgebraicGeometry.Space.essSurjComparison` is compatible with the twist morphism of every
chart of the arrow space. -/
theorem essSurjComparison_twistNaturality
    (hrep : yoneda.relativelyRepresentable φ.hom) (ht : IsEtale B S hS G.target.hom)
    (hs : IsEtale B S hS G.source.hom) (W : SmallEtale B S hS G.arrows.1)
    (n : (essSurjModule B S hS G φ hφet hpb Z).val.obj
      (.op ((smallEtalePostcomp B S hS φ hφet).obj
        ((smallEtalePostcomp B S hS G.target ht).obj W)))) :
    (essSurjComparison B S hS G φ hφet hpb Z).hom.val.app
          (.op ((smallEtalePostcomp B S hS G.source hs).obj W))
        ((essSurjModule B S hS G φ hφet hpb Z).val.map
          (arrowChartTwist B S hS G φ hφet hφ ht hs W).op n) =
      transitionSect B S hS Z.F.obj Z.alpha ht hs W
        ((essSurjComparison B S hS G φ hφet hpb Z).hom.val.app
          (.op ((smallEtalePostcomp B S hS G.target ht).obj W)) n) :=
  (PresheafOfModules.naturality_apply (essSurjCounit B S hS G φ hφet hpb Z).hom.val
      (singleHom B S hS φ hφet (arrowChartTwist B S hS G φ hφet hφ ht hs W)).op n).trans
    ((memberModule_val_map B S hS G φ hφet hpb Z
        (singleHom B S hS φ hφet (arrowChartTwist B S hS G φ hφet hφ ht hs W)) _).trans
      (memberSectMap_arrowChartTwist B S hS G φ hφet hφ hrep hpb Z ht hs W _))

end CoverDense

include hφet in
/-- Every quasi-coherent module on the groupoid is isomorphic to one of the form `(φ^*ℱ, α)`, for
`φ` étale with `t ≫ φ = s ≫ φ`, a surjective étale covering, relatively representable, and with
the arrow space as its kernel pair. -/
theorem exists_spaceBaseObj_iso
    (hcov : IsEtaleCovering B S hS (fun _ : Unit => G.objects.1) (fun _ => φ.hom))
    (hrep : yoneda.relativelyRepresentable φ.hom)
    (hpb : IsPullback G.target.hom G.source.hom φ.hom φ.hom)
    (Z : QuasicoherentModule B S hS G) :
    ∃ F : QuasicoherentSheaves.{u, u} B S hS X.obj X.property,
      Nonempty (spaceBaseObj B S hS G φ hφ F ≅ Z) := by
  have := isCoverDense_singleFunctor B S hS φ hφet hcov
  exact exists_spaceBaseObj_iso_of_etaleComparison B S hS G φ hφet hφ hcov hrep hpb Z
    (isEtale_target B S hS G φ hφet hpb) (isEtale_source B S hS G φ hφet hpb)
    (essSurjModule B S hS G φ hφet hpb Z) (essSurjComparison B S hS G φ hφet hpb Z)
    (essSurjComparison_twistNaturality B S hS G φ hφet hφ hpb Z hrep
      (isEtale_target B S hS G φ hφet hpb) (isEtale_source B S hS G φ hφet hpb))

end Final

end AlgebraicGeometry.Space

end
