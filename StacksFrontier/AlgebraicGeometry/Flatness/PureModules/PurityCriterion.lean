module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Mono
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.RelativeWeakAssassin
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismAssociatedPoints.BaseChange
public import StacksFrontier.AlgebraicGeometry.Divisors.RelativeAssassinTwo.BaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleLocalization.EtalePullback
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningStratification.PurityDescent
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Purity
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.QuasiFinitePointedBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeAssassin.FlatFibreSpecialization
public import StacksFrontier.AlgebraicGeometry.Morphisms.ConstructibleAssociatedPoints05KR
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.Henselization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BaseChangeFiberMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs

/-!
# An étale criterion for purity along a fibre

Let `f : X ⟶ S` be of finite type, let `ℱ` be a finite type quasi-coherent `𝒪_X`-module which is
flat over `S` at every point of the fibre `X_s`, and let `(S', s') ⟶ (S, s)` be an elementary
étale neighbourhood fitting into a commutative square with an étale morphism `g : X' ⟶ X` and a
finite type morphism `X' ⟶ S'`, such that `g^*ℱ` is pure along `X'_{s'}` and `g(X'_{s'})`
contains the associated points `Ass_{X_s}(ℱ_s)`. Then `ℱ` is pure along `X_s` exactly when the
image of `X' ⟶ X ×_S S'` contains every point of the relative assassin
`Ass_{X ×_S S'/S'}(ℱ ×_S S')` lying over a point of `S'` which specializes to `s'`.

The source states hypothesis (5) as `g(X') ⊇ Ass_{X_s}(ℱ_s)`, without asking that the points of
`X'` hitting `Ass_{X_s}(ℱ_s)` lie over `s'`. Read that way the statement is false: when `S'` has a
second point over `s` and `X'` lies over it, nothing ties `X'` to `s'`. The counterexample is
`Stacks.Examples.not_forall_isPureAlong_iff_of_associatedPoints_subset_range`. The proof of the
source replaces `S` by `S'` and so uses hypothesis (5) for the fibre over `s'`, which is the form
stated here.

## Main results

* `AlgebraicGeometry.isPureAlong_iff_relativeAssassin_specializing_mem_range_of_associatedPoints`
  is the criterion.
* `AlgebraicGeometry.isPureAlong_iff_relativeAssassin_specializing_mem_range` is the same
  criterion with hypothesis (5) phrased on the fibre of `X ×_S S' ⟶ S'` over `s'`.
* `AlgebraicGeometry.baseChangeFiber_fst_injective`: a point of the fibre of a base change over a
  point with the same residue field as its image is determined by its image in the original
  source.

## Implementation notes

The elementary étale neighbourhood is an `AlgebraicGeometry.EtaleNeighborhood` together with
`AlgebraicGeometry.EtaleNeighborhood.IsElementary`, the base change `X ×_S S'` is the chosen
categorical pullback, and the morphism `X' ⟶ X ×_S S'` induced by the commutative square is the
corresponding `CategoryTheory.Limits.pullback.lift`.

Purity of the base change along `(X ×_S S')_{s'}` is obtained from purity along `X_s` through
Tag 05J7, applied to the étale and hence quasi-finite structure morphism of the neighbourhood,
and purity along `X_s` is recovered from it by the flat descent of Tag 05J9. Neither direction
passes to the henselization of the local ring of `S` at `s`: in the harder direction an impurity
of the base change is transported along the étale morphism `X' ⟶ X ×_S S'` by pulling it back
and choosing a point of the residue-field tensor product of the chosen lift, which contradicts
purity of `g^*ℱ` directly.

Hypothesis (5) is moved to the fibre of `X ×_S S'` over `s'` through Tag 05DC, which places the
image in `X` of an associated point of that fibre in `Ass_{X_s}(ℱ_s)`, and through the fact that
the fibre of `X ×_S S'` over `s'` maps injectively to `X`, the residue fields of `s` and `s'`
being equal.

## References

* [Stacks Project, Tag 05L4](https://stacks.math.columbia.edu/tag/05L4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The morphism of fibres over `s` induced by a morphism `i : A ⟶ B` of schemes over `S`. -/
def fiberMapOfSource {A B S : Scheme.{u}} (i : A ⟶ B) (f : B ⟶ S) (s : S) :
    (i ≫ f).fiber s ⟶ f.fiber s :=
  pullback.lift ((i ≫ f).fiberι s ≫ i) ((i ≫ f).fiberToSpecResidueField s) (by
    calc
      ((i ≫ f).fiberι s ≫ i) ≫ f = (i ≫ f).fiberι s ≫ (i ≫ f) := by
        simp [Category.assoc]
      _ = (i ≫ f).fiberToSpecResidueField s ≫ S.fromSpecResidueField s :=
        Scheme.Hom.fiber_fac (i ≫ f) s)

/-- The morphism of fibres induced by `i` is compatible with the inclusions of the fibres. -/
theorem fiberMapOfSource_fiberι {A B S : Scheme.{u}} (i : A ⟶ B) (f : B ⟶ S) (s : S) :
    fiberMapOfSource i f s ≫ f.fiberι s = (i ≫ f).fiberι s ≫ i := by
  dsimp [fiberMapOfSource, Scheme.Hom.fiber, Scheme.Hom.fiberι]
  exact pullback.lift_fst _ _ _

/-- The morphism of fibres induced by `i : A ⟶ B` is a base change of `i` itself. -/
theorem fiberMapOfSource_isPullback {A B S : Scheme.{u}} (i : A ⟶ B) (f : B ⟶ S)
    (s : S) :
    IsPullback (fiberMapOfSource i f s) ((i ≫ f).fiberι s) (f.fiberι s) i := by
  have hOuter : IsPullback ((i ≫ f).fiberToSpecResidueField s) ((i ≫ f).fiberι s)
      (S.fromSpecResidueField s) (i ≫ f) :=
    (IsPullback.of_hasPullback (i ≫ f) (S.fromSpecResidueField s)).flip
  have hRight : IsPullback (pullback.snd f (S.fromSpecResidueField s))
      (pullback.fst f (S.fromSpecResidueField s)) (S.fromSpecResidueField s) f :=
    (IsPullback.of_hasPullback f (S.fromSpecResidueField s)).flip
  have hsnd : fiberMapOfSource i f s ≫ pullback.snd f (S.fromSpecResidueField s) =
      pullback.snd (i ≫ f) (S.fromSpecResidueField s) := by
    dsimp [fiberMapOfSource, Scheme.Hom.fiber, Scheme.Hom.fiberToSpecResidueField]
    exact pullback.lift_snd _ _ _
  have hfst : fiberMapOfSource i f s ≫ pullback.fst f (S.fromSpecResidueField s) =
      (i ≫ f).fiberι s ≫ i := by
    dsimp [fiberMapOfSource, Scheme.Hom.fiber, Scheme.Hom.fiberι]
    exact pullback.lift_fst _ _ _
  have hOuter' : IsPullback
      (fiberMapOfSource i f s ≫ pullback.snd f (S.fromSpecResidueField s))
      (pullback.fst (i ≫ f) (S.fromSpecResidueField s)) (S.fromSpecResidueField s) (i ≫ f) := by
    rw [hsnd]
    exact hOuter
  exact IsPullback.of_right hOuter' hfst hRight

/-- Restricting a module to a fibre of `f` and pulling back along the induced morphism of fibres
agrees with pulling back along `i` and restricting to the corresponding fibre of `i ≫ f`. -/
def fiberModuleIsoOfSource {A B S : Scheme.{u}} (i : A ⟶ B) (f : B ⟶ S)
    (F : B.Modules) (s : S) :
    (Scheme.Modules.pullback (fiberMapOfSource i f s)).obj
        ((Scheme.Modules.pullback (f.fiberι s)).obj F) ≅
      (Scheme.Modules.pullback ((i ≫ f).fiberι s)).obj ((Scheme.Modules.pullback i).obj F) :=
  (Scheme.Modules.pullbackComp (fiberMapOfSource i f s) (f.fiberι s)).app F ≪≫
    (Scheme.Modules.pullbackCongr (fiberMapOfSource_fiberι i f s)).app F ≪≫
      ((Scheme.Modules.pullbackComp ((i ≫ f).fiberι s) i).app F).symm

/-- The pullback of a quasi-coherent module along a morphism of schemes is quasi-coherent. -/
private theorem pullback_isQuasicoherent_obj {X Y : Scheme.{u}} (g : Y ⟶ X) (F : X.Modules)
    [F.IsQuasicoherent] : ((Scheme.Modules.pullback g).obj F).IsQuasicoherent :=
  @SheafOfModules.modulePullback_isQuasicoherent _ _ g.toLRSHom.toShHom F
    (show F.IsQuasicoherent from inferInstance)

/-- For `i` étale, a point lies in the relative assassin of the pullback of `F` along `i`
relative to `i ≫ f` exactly when its image lies in the relative assassin of `F` relative
to `f`. -/
theorem mem_relativeAssassin_comp_iff_of_etale {A B S : Scheme.{u}} (i : A ⟶ B)
    [Etale i] (f : B ⟶ S) [LocallyOfFiniteType f] (F : B.Modules) [F.IsQuasicoherent] (y : A) :
    y ∈ Stacks.Divisors.relativeAssassin (i ≫ f) ((Scheme.Modules.pullback i).obj F) ↔
      i y ∈ Stacks.Divisors.relativeAssassin f F := by
  have : ((Scheme.Modules.pullback i).obj F).IsQuasicoherent := pullback_isQuasicoherent_obj i F
  have : ∀ s, Etale (fiberMapOfSource i f s) := fun s =>
    MorphismProperty.of_isPullback (fiberMapOfSource_isPullback i f s).flip inferInstance
  rw [← relativeWeaklyAssociatedPoints_eq_relativeAssassin (i ≫ f)
      ((Scheme.Modules.pullback i).obj F),
    ← relativeWeaklyAssociatedPoints_eq_relativeAssassin f F]
  show y ∈ relativeWeaklyAssociatedPoints (i ≫ f) ((Scheme.Modules.pullback i).obj F) ↔
    i y ∈ relativeWeaklyAssociatedPoints f F
  simp only [relativeWeaklyAssociatedPoints, Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨s, z, hz, hzy⟩
    have : ((Scheme.Modules.pullback (f.fiberι s)).obj F).IsQuasicoherent :=
      pullback_isQuasicoherent_obj (f.fiberι s) F
    have hzM : Stacks.Divisors.IsWeaklyAssociatedPoint
        ((Scheme.Modules.pullback (fiberMapOfSource i f s)).obj
          ((Scheme.Modules.pullback (f.fiberι s)).obj F)) z :=
      (isWeaklyAssociatedPoint_iff_of_iso (fiberModuleIsoOfSource i f F s).symm z).mp hz
    have hfp := (isWeaklyAssociatedPoint_pullback_iff_of_etale (fiberMapOfSource i f s)
      ((Scheme.Modules.pullback (f.fiberι s)).obj F) z).mp hzM
    refine ⟨s, (fiberMapOfSource i f s).base z, hfp, ?_⟩
    calc
      f.fiberι s ((fiberMapOfSource i f s).base z) = i ((i ≫ f).fiberι s z) :=
        congrArg (fun k : (i ≫ f).fiber s ⟶ B => k z) (fiberMapOfSource_fiberι i f s)
      _ = i y := congrArg i hzy
  · rintro ⟨s, z, hz, hzy⟩
    have : ((Scheme.Modules.pullback (f.fiberι s)).obj F).IsQuasicoherent :=
      pullback_isQuasicoherent_obj (f.fiberι s) F
    have hybase : (i ≫ f) y = s := by
      calc
        (i ≫ f) y = f (i y) := rfl
        _ = s := by rw [← hzy]; exact f.apply_fiberι s z
    refine ⟨s, ((i ≫ f).fiberHomeo s).symm ⟨y, hybase⟩, ?_, ?_⟩
    · have hw : (fiberMapOfSource i f s).base (((i ≫ f).fiberHomeo s).symm ⟨y, hybase⟩) = z := by
        apply (f.fiberι s).isEmbedding.injective
        calc
          f.fiberι s ((fiberMapOfSource i f s).base
              (((i ≫ f).fiberHomeo s).symm ⟨y, hybase⟩)) =
              i ((i ≫ f).fiberι s (((i ≫ f).fiberHomeo s).symm ⟨y, hybase⟩)) :=
            congrArg (fun k : (i ≫ f).fiber s ⟶ B => k (((i ≫ f).fiberHomeo s).symm ⟨y, hybase⟩))
              (fiberMapOfSource_fiberι i f s)
          _ = i y := congrArg i ((i ≫ f).fiberι_fiberHomeo_symm s ⟨y, hybase⟩)
          _ = f.fiberι s z := hzy.symm
      have hM : Stacks.Divisors.IsWeaklyAssociatedPoint
          ((Scheme.Modules.pullback (fiberMapOfSource i f s)).obj
            ((Scheme.Modules.pullback (f.fiberι s)).obj F))
          (((i ≫ f).fiberHomeo s).symm ⟨y, hybase⟩) :=
        (isWeaklyAssociatedPoint_pullback_iff_of_etale (fiberMapOfSource i f s)
            ((Scheme.Modules.pullback (f.fiberι s)).obj F)
            (((i ≫ f).fiberHomeo s).symm ⟨y, hybase⟩)).mpr
          ((congrArg (Stacks.Divisors.IsWeaklyAssociatedPoint
            ((Scheme.Modules.pullback (f.fiberι s)).obj F)) hw).to_iff.mpr hz)
      exact (isWeaklyAssociatedPoint_iff_of_iso (fiberModuleIsoOfSource i f F s) _).mp hM
    · exact (i ≫ f).fiberι_fiberHomeo_symm s ⟨y, hybase⟩

/-- Purity along the fibre over the distinguished point forces every point of the relative
assassin lying over a generalization of that point to specialize into the fibre: otherwise the
identity base change exhibits an impurity. -/
theorem exists_specializes_fiberι_of_isPureAlong (P : PrePureSituation.{u})
    (hP : IsPureAlong P) {x : P.X} (hx : x ∈ Stacks.Divisors.relativeAssassin P.f P.F)
    (hbase : P.f.base x ⤳ P.s) :
    ∃ y : P.f.fiber P.s, x ⤳ P.f.fiberι P.s y := by
  classical
  by_contra hspec
  refine hP
    { T := P.S
      g := 𝟙 P.S
      t' := P.f.base x
      t := P.s
      specializes := hbase
      mapsToChosenPoint := by simp
      X_T := P.X
      toX := 𝟙 P.X
      toT := P.f
      isPullback := IsPullback.id_horiz P.f
      xi := x
      xi_liesOver := rfl } inferInstance
    (EtaleNeighborhood.isElementary_self P.S P.s) ⟨?_, ?_⟩
  · show x ∈ Stacks.Divisors.relativeAssassin P.f ((Scheme.Modules.pullback (𝟙 P.X)).obj P.F)
    rw [relativeAssassin_eq_of_moduleIso P.f ((Scheme.Modules.pullbackId P.X).app P.F)]
    exact hx
  · refine Set.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
    obtain ⟨y, rfl⟩ := hz.2
    exact hspec ⟨y, specializes_iff_mem_closure.mpr hz.1⟩

/-- A section of an étale morphism is an open immersion. -/
@[ega "IV 17.9.3"]
theorem isOpenImmersion_of_section {X Y : Scheme.{u}} (p : X ⟶ Y) [Etale p] (t : Y ⟶ X)
    (ht : t ≫ p = 𝟙 Y) : IsOpenImmersion t := by
  have : Etale (t ≫ p) := ht ▸ inferInstance
  have : Etale t := Etale.of_comp t p
  have : Mono t := mono_of_mono_fac ht
  exact IsOpenImmersion.of_flat_of_mono t

/-- A point of a fibre of the base change `X ×_Y Y' ⟶ Y'` over `z` maps to `g z` in `Y`
through `X`. -/
private theorem apply_fst_fiberι_pullback {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (z : Y')
    (w : (pullback.snd f g).fiber z) :
    f (pullback.fst f g ((pullback.snd f g).fiberι z w)) = g z := by
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply,
    (pullback.snd f g).apply_fiberι]

/-- The morphism `X' ⟶ X ×_S S'` induced by a commutative square whose horizontal morphisms
`X' ⟶ X` and `S' ⟶ S` are étale is itself étale. -/
private theorem etale_pullback_lift {X S X' U : Scheme.{u}} (f : X ⟶ S) (UtoS : U ⟶ S)
    (g : X' ⟶ X) (p : X' ⟶ U) (hcomm : g ≫ f = p ≫ UtoS) [Etale UtoS] [Etale g] :
    Etale (pullback.lift g p hcomm) := by
  have hsec : pullback.lift g p hcomm ≫ pullback.fst f UtoS = g := pullback.lift_fst _ _ _
  have hsection : pullback.lift (𝟙 X') (pullback.lift g p hcomm)
        (by rw [Category.id_comp, hsec]) ≫ pullback.fst g (pullback.fst f UtoS) = 𝟙 X' :=
    pullback.lift_fst _ _ _
  have : Etale (pullback.fst g (pullback.fst f UtoS)) := inferInstance
  have : IsOpenImmersion (pullback.lift (𝟙 X') (pullback.lift g p hcomm)
      (by rw [Category.id_comp, hsec])) :=
    isOpenImmersion_of_section _ _ hsection
  have : Etale (pullback.snd g (pullback.fst f UtoS)) := inferInstance
  have hq : pullback.lift g p hcomm = pullback.lift (𝟙 X') (pullback.lift g p hcomm)
      (by rw [Category.id_comp, hsec]) ≫ pullback.snd g (pullback.fst f UtoS) :=
    (pullback.lift_snd _ _ _).symm
  rw [hq]
  infer_instance

/-- For an elementary étale neighbourhood the residue field map of the structure morphism at the
distinguished point is an isomorphism. This is
`AlgebraicGeometry.EtaleNeighborhood.isElementary_iff` read in the direction the fibre comparison
needs: the transport along `EtaleNeighborhood.map_point` built into
`AlgebraicGeometry.EtaleNeighborhood.residueFieldMap` is itself an isomorphism, so it does not
affect the condition. -/
alias isIso_toBase_residueFieldMap_of_isElementary :=
  AlgebraicGeometry.toBase_residueFieldMap_isIso_of_elementary

/-- A point of the fibre of the base change `X ×_Y Y' ⟶ Y'` over a point `z` at which the residue
field of `Y'` agrees with that of its image in `Y` is determined by its image in `X`.

This is injectivity of `AlgebraicGeometry.baseChangeFiberMap` — which the residue field
hypothesis makes an isomorphism — read through
`AlgebraicGeometry.baseChangeFiberMap_comp_fiberι`, the fibre inclusion `X_{g z} ⟶ X` being a
preimmersion and hence injective. -/
theorem baseChangeFiber_fst_injective {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (z : Y')
    [IsIso (g.residueFieldMap z)] :
    Function.Injective fun w : (pullback.snd f g).fiber z =>
      pullback.fst f g ((pullback.snd f g).fiberι z w) := by
  have hiso : IsIso (baseChangeFiberMap f g z) := isIso_baseChangeFiberMap f g z
  have key : ∀ w : (pullback.snd f g).fiber z,
      f.fiberι (g z) (baseChangeFiberMap f g z w) =
        pullback.fst f g ((pullback.snd f g).fiberι z w) := by
    intro w
    have h := congrArg (fun m : (pullback.snd f g).fiber z ⟶ X => m w)
      (baseChangeFiberMap_comp_fiberι f g z)
    simpa [Scheme.Hom.comp_apply] using h
  intro w₁ w₂ h
  have h2 : f.fiberι (g z) (baseChangeFiberMap f g z w₁)
      = f.fiberι (g z) (baseChangeFiberMap f g z w₂) := by
    rwa [key, key]
  exact (baseChangeFiberMap f g z).homeomorph.injective
    ((f.fiberι (g z)).isEmbedding.injective h2)

/-- A point `y` of `X'` lying over the distinguished point of an elementary étale neighbourhood
and mapping to the image in `X` of a point `z` of the fibre of `X ×_S S' ⟶ S'` over that point is
sent to `z` by the morphism `X' ⟶ X ×_S S'` induced by the commutative square.

Both points lie in the fibre over the distinguished point and have the same image in `X`, so they
agree by `AlgebraicGeometry.baseChangeFiber_fst_injective`. -/
theorem pullbackLift_eq_fiberι_of_fst_eq {X S X' : Scheme.{u}} (f : X ⟶ S) {s : S}
    (U : EtaleNeighborhood S s) (hU : U.IsElementary)
    (p : X' ⟶ U.scheme) (g : X' ⟶ X) (hcomm : g ≫ f = p ≫ U.toBase)
    (z : (pullback.snd f U.toBase).fiber U.point) (y : X') (hpy : p y = U.point)
    (hgy : g y = pullback.fst f U.toBase ((pullback.snd f U.toBase).fiberι U.point z)) :
    pullback.lift g p hcomm y = (pullback.snd f U.toBase).fiberι U.point z := by
  have : IsIso (U.toBase.residueFieldMap U.point) :=
    isIso_toBase_residueFieldMap_of_isElementary U hU
  have hmem : pullback.lift g p hcomm y ∈ (pullback.snd f U.toBase) ⁻¹' {U.point} := by
    show (pullback.snd f U.toBase) (pullback.lift g p hcomm y) = U.point
    rw [← Scheme.Hom.comp_apply, pullback.lift_snd, hpy]
  obtain ⟨z', hz'⟩ := ((pullback.snd f U.toBase).range_fiberι U.point).ge hmem
  have hzz : z' = z := by
    refine baseChangeFiber_fst_injective f U.toBase U.point ?_
    show pullback.fst f U.toBase ((pullback.snd f U.toBase).fiberι U.point z')
      = pullback.fst f U.toBase ((pullback.snd f U.toBase).fiberι U.point z)
    rw [hz', ← Scheme.Hom.comp_apply, pullback.lift_fst, hgy]
  rw [← hz', hzz]

/-- The purity criterion of Tag 05L4 with hypothesis (5) phrased on the fibre of the base change.
Let `f : X ⟶ S` be of finite type, let `ℱ` be a finite type quasi-coherent `𝒪_X`-module flat over
`S` at every point of `X_s`, and let a commutative square present an étale `g : X' ⟶ X` over an
elementary étale neighbourhood `(S', s')` of `(S, s)` with `X' ⟶ S'` of finite type and `g^*ℱ`
pure along `X'_{s'}`, such that the image of `X' ⟶ X ×_S S'` contains the associated points of
`(ℱ ×_S S')_{s'}`. Then `ℱ` is pure along `X_s` if and only if that image contains every point
of `Ass_{X ×_S S'/S'}(ℱ ×_S S')` lying over a point of `S'` specializing to `s'`.

The hypothesis on the fibre over `s'` is equivalent to asking that `g(X'_{s'})` contain
`Ass_{X_s}(ℱ_s)`, which is the form of
`AlgebraicGeometry.isPureAlong_iff_relativeAssassin_specializing_mem_range_of_associatedPoints`.
The implication from the containment to purity does not use it. -/
public theorem isPureAlong_iff_relativeAssassin_specializing_mem_range
    {X S X' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (s : S) (U : EtaleNeighborhood S s) (_hU : U.IsElementary)
    (p : X' ⟶ U.scheme) [LocallyOfFiniteType p] [QuasiCompact p]
    (g : X' ⟶ X) [Etale g] (hcomm : g ≫ f = p ≫ U.toBase)
    (hflat : ∀ x : f.fiber s, IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s x))
    (hpure' : IsPureAlong
      ({ S := U.scheme
         X := X'
         f := p
         F := (Scheme.Modules.pullback g).obj F
         isFiniteType := SheafOfModules.pullback_isFiniteType g.toLRSHom.toShHom F
         isQuasicoherent := by
           have hF : F.IsQuasicoherent := inferInstance
           exact @SheafOfModules.modulePullback_isQuasicoherent X'.toRingedSpace
             X.toRingedSpace g.toLRSHom.toShHom F hF
         s := U.point } : PrePureSituation.{u}))
    (hcover : ∀ z : (pullback.snd f U.toBase).fiber U.point,
      z ∈ Stacks.Divisors.associatedPoints
          ((Scheme.Modules.pullback ((pullback.snd f U.toBase).fiberι U.point)).obj
            ((Scheme.Modules.pullback (pullback.fst f U.toBase)).obj F)) →
        ∃ y : X', pullback.lift g p hcomm y =
          (pullback.snd f U.toBase).fiberι U.point z) :
    IsPureAlong ({ S := S, X := X, f := f, F := F, s := s } : PrePureSituation.{u}) ↔
      ∀ x : pullback (C := Scheme.{u}) f U.toBase,
        x ∈ Stacks.Divisors.relativeAssassin (pullback.snd f U.toBase)
            ((Scheme.Modules.pullback (pullback.fst f U.toBase)).obj F) →
          pullback.snd f U.toBase x ⤳ U.point →
            x ∈ Set.range (pullback.lift g p hcomm) := by
  classical
  have hFqc : F.IsQuasicoherent := inferInstance
  let Q : PrePureSituation.{u} :=
    { S := U.scheme
      X := pullback f U.toBase
      f := pullback.snd f U.toBase
      F := (Scheme.Modules.pullback (pullback.fst f U.toBase)).obj F
      isFiniteType := SheafOfModules.pullback_isFiniteType
        (pullback.fst f U.toBase).toLRSHom.toShHom F
      isQuasicoherent := pullback_isQuasicoherent_obj (pullback.fst f U.toBase) F
      s := U.point }
  let P' : PrePureSituation.{u} :=
    { S := U.scheme
      X := X'
      f := p
      F := (Scheme.Modules.pullback g).obj F
      isFiniteType := SheafOfModules.pullback_isFiniteType g.toLRSHom.toShHom F
      isQuasicoherent := pullback_isQuasicoherent_obj g F
      s := U.point }
  have hqfst : pullback.lift g p hcomm ≫ pullback.fst f U.toBase = g :=
    pullback.lift_fst _ _ _
  have hqsnd : pullback.lift g p hcomm ≫ pullback.snd f U.toBase = p :=
    pullback.lift_snd _ _ _
  have hqEtale : Etale (pullback.lift g p hcomm) := etale_pullback_lift f U.toBase g p hcomm
  have : LocallyOfFiniteType (pullback.snd f U.toBase) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f U.toBase) inferInstance
  have hbaseZ : ∀ z : (pullback.snd f U.toBase).fiber U.point,
      f (pullback.fst f U.toBase ((pullback.snd f U.toBase).fiberι U.point z)) = s := fun z =>
    (apply_fst_fiberι_pullback f U.toBase U.point z).trans U.map_point
  constructor
  · intro hpure x hx hspec
    have hqf : quasiFiniteAt U.toBase U.point := by
      obtain ⟨_, _⟩ := locallyQuasiFinite_of_etale U.toBase
      exact (forall_quasiFiniteAt_iff U.toBase).2 ⟨inferInstance, inferInstance⟩ U.point
    have hpureQ : IsPureAlong Q :=
      isPureAlong_of_quasiFiniteAt_of_isPureAlong
        (P := ({ S := S, X := X, f := f, F := F, s := s } : PrePureSituation.{u})) (Q := Q)
        U.toBase U.map_point (pullback.fst f U.toBase)
        (IsPullback.of_hasPullback f U.toBase) (Iso.refl _) hqf hpure
    have hQx : x ∈ Stacks.Divisors.relativeAssassin Q.f Q.F := hx
    obtain ⟨t, hxt⟩ := exists_specializes_fiberι_of_isPureAlong Q hpureQ hQx hspec
    have hflatQ : ∀ z : Q.f.fiber Q.s,
        IsFlatOverAt Q.f.toLRSHom.toShHom Q.F (Q.f.fiberι Q.s z) := by
      intro z
      have hxFiber : f.fiberι s ((f.fiberHomeo s).symm
          ⟨pullback.fst f U.toBase ((pullback.snd f U.toBase).fiberι U.point z),
            hbaseZ z⟩) =
          pullback.fst f U.toBase ((pullback.snd f U.toBase).fiberι U.point z) :=
        f.fiberι_fiberHomeo_symm s _
      have hflatX : IsFlatOverAt f.toLRSHom.toShHom F
          (pullback.fst f U.toBase ((pullback.snd f U.toBase).fiberι U.point z)) := by
        simpa only [hxFiber] using hflat ((f.fiberHomeo s).symm
          ⟨pullback.fst f U.toBase ((pullback.snd f U.toBase).fiberι U.point z), hbaseZ z⟩)
      let F₀ : SheafOfModules.{u} (structureSheafRing X.toRingedSpace) := F
      let : F₀.IsQuasicoherent := hFqc
      have h := modulePullback_isFlatOverAt (IsPullback.of_hasPullback f U.toBase) F₀
        ((pullback.snd f U.toBase).fiberι U.point z) hflatX
      let e : (RingedSpaceModuleAdjunction.modulePullback
          (pullback.fst f U.toBase).toLRSHom.toShHom).obj F₀ ≅
            (Scheme.Modules.pullback (pullback.fst f U.toBase)).obj F :=
        ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
          (pullback.fst f U.toBase).toLRSHom.toShHom).leftAdjointUniq
          (Scheme.Modules.pullbackPushforwardAdjunction (pullback.fst f U.toBase))).app F
      exact isFlatOverAt_of_moduleIso (pullback.snd f U.toBase).toLRSHom.toShHom e
        ((pullback.snd f U.toBase).fiberι U.point z) h
    obtain ⟨z, hspecial, hzass⟩ :=
      Stacks.RelativeAssassin.exists_specializes_mem_associatedPoints_fibre Q.f Q.F Q.s
        hflatQ hQx ⟨t, hxt⟩
    have hzrange : (pullback.snd f U.toBase).fiberι U.point z ∈
        Set.range (pullback.lift g p hcomm) := hcover z hzass
    have hOpen : IsOpen (Set.range (pullback.lift g p hcomm)) :=
      (Scheme.Hom.isOpenMap (pullback.lift g p hcomm)).isOpen_range
    by_contra hnot
    exact hOpen.not_specializes hnot hzrange hspecial
  · intro hRange
    have hQpure : IsPureAlong Q := by
      intro D hD hDElem hDimp
      have hEfst : D.isPullback.isoPullback.hom ≫ pullback.fst Q.f D.g = D.toX := by
        simp
      have hEsnd : D.isPullback.isoPullback.hom ≫ pullback.snd Q.f D.g = D.toT := by
        simp
      have : Etale D.isPullback.isoPullback.hom := inferInstance
      have hrelD : D.xi ∈ Stacks.Divisors.relativeAssassin
          (D.isPullback.isoPullback.hom ≫ pullback.snd Q.f D.g)
          ((Scheme.Modules.pullback D.isPullback.isoPullback.hom).obj
            ((Scheme.Modules.pullback (pullback.fst Q.f D.g)).obj Q.F)) := by
        have hmem := (relativeAssassin_eq_of_moduleIso D.toT
          ((Scheme.Modules.pullbackComp D.isPullback.isoPullback.hom
              (pullback.fst Q.f D.g)).app Q.F ≪≫
            (Scheme.Modules.pullbackCongr hEfst).app Q.F)).symm ▸ hDimp.1
        simpa [hEsnd] using hmem
      have : ((Scheme.Modules.pullback (pullback.fst Q.f D.g)).obj Q.F).IsQuasicoherent :=
        pullback_isQuasicoherent_obj _ Q.F
      have hrelCanon := (mem_relativeAssassin_comp_iff_of_etale D.isPullback.isoPullback.hom
        (pullback.snd Q.f D.g)
        ((Scheme.Modules.pullback (pullback.fst Q.f D.g)).obj Q.F) D.xi).mp hrelD
      have hdc := (mem_relativeAssassin_pullback_iff Q.f D.g Q.F
        (D.isPullback.isoPullback.hom D.xi)).mp hrelCanon
      have hfstPoint : pullback.fst Q.f D.g (D.isPullback.isoPullback.hom D.xi) = D.toX D.xi :=
        congrArg (fun k : D.X_T ⟶ Q.X => k D.xi) hEfst
      have hxrel : D.toX D.xi ∈ Stacks.Divisors.relativeAssassin Q.f Q.F := by
        simpa [hfstPoint] using hdc.1
      have hbase : Q.f (D.toX D.xi) = D.g D.t' := by
        have hw := congrArg (fun k : D.X_T ⟶ U.scheme => k D.xi) D.isPullback.w
        simpa [D.xi_liesOver] using hw
      have hspecU : Q.f (D.toX D.xi) ⤳ U.point := by
        simpa [D.mapsToChosenPoint, hbase] using D.specializes.map D.g.continuous
      obtain ⟨y, hy⟩ := hRange (D.toX D.xi) hxrel hspecU
      have hA : IsPullback (pullback.fst (pullback.lift g p hcomm) D.toX)
          (pullback.snd (pullback.lift g p hcomm) D.toX) (pullback.lift g p hcomm) D.toX :=
        IsPullback.of_hasPullback _ _
      have : Etale (pullback.snd (pullback.lift g p hcomm) D.toX) :=
        MorphismProperty.of_isPullback hA inferInstance
      have hA' : IsPullback (pullback.fst (pullback.lift g p hcomm) D.toX)
          (pullback.snd (pullback.lift g p hcomm) D.toX ≫ D.toT) p D.g := by
        have hpaste := hA.paste_vert D.isPullback
        change IsPullback (pullback.fst (pullback.lift g p hcomm) D.toX)
          (pullback.snd (pullback.lift g p hcomm) D.toX ≫ D.toT)
          (pullback.lift g p hcomm ≫ pullback.snd f U.toBase) D.g at hpaste
        rwa [hqsnd] at hpaste
      obtain ⟨p₀⟩ : Nonempty (PrimeSpectrum
          ((Scheme.Pullback.Triplet.mk' y D.xi hy).tensor : Type u)) := inferInstance
      have hvxi : pullback.snd (pullback.lift g p hcomm) D.toX
          ((Scheme.Pullback.Triplet.mk' y D.xi hy).SpecTensorTo p₀) = D.xi :=
        (Scheme.Pullback.Triplet.mk' y D.xi hy).snd_SpecTensorTo_apply p₀
      have hmap : pullback.fst (pullback.lift g p hcomm) D.toX ≫ g =
          (pullback.snd (pullback.lift g p hcomm) D.toX ≫ D.toX) ≫
            pullback.fst f U.toBase := by
        calc
          pullback.fst (pullback.lift g p hcomm) D.toX ≫ g =
              pullback.fst (pullback.lift g p hcomm) D.toX ≫
                pullback.lift g p hcomm ≫ pullback.fst f U.toBase := by rw [hqfst]
          _ = (pullback.fst (pullback.lift g p hcomm) D.toX ≫ pullback.lift g p hcomm) ≫
                pullback.fst f U.toBase := by simp [Category.assoc]
          _ = (pullback.snd (pullback.lift g p hcomm) D.toX ≫ D.toX) ≫
                pullback.fst f U.toBase := by rw [hA.w]
      have : LocallyOfFiniteType D.toT :=
        MorphismProperty.of_isPullback D.isPullback inferInstance
      have : (D.pulledBack Q).IsQuasicoherent := pullback_isQuasicoherent_obj D.toX Q.F
      let D' : ImpurityDiagram P' :=
        { T := D.T
          g := D.g
          t' := D.t'
          t := D.t
          specializes := D.specializes
          mapsToChosenPoint := D.mapsToChosenPoint
          X_T := pullback (pullback.lift g p hcomm) D.toX
          toX := pullback.fst (pullback.lift g p hcomm) D.toX
          toT := pullback.snd (pullback.lift g p hcomm) D.toX ≫ D.toT
          isPullback := hA'
          xi := (Scheme.Pullback.Triplet.mk' y D.xi hy).SpecTensorTo p₀
          xi_liesOver := by
            rw [Scheme.Hom.comp_apply, hvxi]
            exact D.xi_liesOver }
      have hrelA : (Scheme.Pullback.Triplet.mk' y D.xi hy).SpecTensorTo p₀ ∈
          Stacks.Divisors.relativeAssassin
            (pullback.snd (pullback.lift g p hcomm) D.toX ≫ D.toT)
            ((Scheme.Modules.pullback
              (pullback.snd (pullback.lift g p hcomm) D.toX)).obj (D.pulledBack Q)) := by
        apply (mem_relativeAssassin_comp_iff_of_etale
          (pullback.snd (pullback.lift g p hcomm) D.toX) D.toT (D.pulledBack Q) _).mpr
        simpa [hvxi] using hDimp.1
      have hrelD' : D'.xi ∈ Stacks.Divisors.relativeAssassin D'.toT (D'.pulledBack P') :=
        (relativeAssassin_eq_of_moduleIso (pullback.snd (pullback.lift g p hcomm) D.toX ≫ D.toT)
          ((Scheme.Modules.pullbackComp
              (pullback.fst (pullback.lift g p hcomm) D.toX) g).app F ≪≫
            (Scheme.Modules.pullbackCongr hmap).app F ≪≫
              ((Scheme.Modules.pullbackComp
                (pullback.snd (pullback.lift g p hcomm) D.toX ≫ D.toX)
                (pullback.fst f U.toBase)).app F).symm ≪≫
                ((Scheme.Modules.pullbackComp
                  (pullback.snd (pullback.lift g p hcomm) D.toX) D.toX).app Q.F).symm)).symm ▸
          hrelA
      have hdisj : closure {(Scheme.Pullback.Triplet.mk' y D.xi hy).SpecTensorTo p₀} ∩
          Set.range ((pullback.snd (pullback.lift g p hcomm) D.toX ≫ D.toT).fiberι D.t) = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
        have hspecV : D.xi ⤳ pullback.snd (pullback.lift g p hcomm) D.toX z := by
          rw [← hvxi]
          exact (specializes_iff_mem_closure.mpr hz.1).map
            (pullback.snd (pullback.lift g p hcomm) D.toX).continuous
        have hzbase : D.toT (pullback.snd (pullback.lift g p hcomm) D.toX z) = D.t := by
          have hz' : z ∈ Set.range
              ((pullback.snd (pullback.lift g p hcomm) D.toX ≫ D.toT).fiberι D.t) := hz.2
          rw [Scheme.Hom.range_fiberι] at hz'
          simpa [Scheme.Hom.comp_apply] using
            Set.mem_singleton_iff.mp (Set.mem_preimage.mp hz')
        have hbad : pullback.snd (pullback.lift g p hcomm) D.toX z ∈
            closure {D.xi} ∩ Set.range (D.toT.fiberι D.t) :=
          ⟨specializes_iff_mem_closure.mp hspecV, by
            rw [D.toT.range_fiberι]
            exact Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr hzbase)⟩
        rw [hDimp.2] at hbad
        exact hbad
      exact hpure' D' hD hDElem ⟨hrelD', hdisj⟩
    exact isPureAlong_of_flatPointedBaseChange
      { X := X
        S := S
        f := f
        F := F
        s := s
        S' := U.scheme
        s' := U.point
        g := U.toBase
        mapsTo := U.map_point
        flatAt := Flat.stalkMap U.toBase U.point } Q rfl rfl (by simp [Q]) (HEq.refl _) rfl
      hQpure

/-- **Stacks Project, Tag 05L4.** Let `f : X ⟶ S` be of finite type, let `ℱ` be a finite type
quasi-coherent `𝒪_X`-module and let `s ∈ S`. Let `(S', s') ⟶ (S, s)` be an elementary étale
neighbourhood and let `g : X' ⟶ X` and `p : X' ⟶ S'` form a commutative square over `S' ⟶ S`.
Assume

1. `ℱ` is flat over `S` at all points of `X_s`,
2. `p : X' ⟶ S'` is of finite type,
3. `g^*ℱ` is pure along `X'_{s'}`,
4. `g : X' ⟶ X` is étale, and
5. `g(X'_{s'})` contains `Ass_{X_s}(ℱ_s)`.

Then `ℱ` is pure along `X_s` if and only if the image of `X' ⟶ X ×_S S'` contains the points of
`Ass_{X ×_S S'/S'}(ℱ ×_S S')` lying over points of `S'` which specialize to `s'`.

The source states (5) as `g(X') ⊇ Ass_{X_s}(ℱ_s)`. With that reading the statement is false, by
`Stacks.Examples.not_forall_isPureAlong_iff_of_associatedPoints_subset_range`: take
`X = S`, `ℱ = 𝒪_S`, `S' = S ⨿ S` with `s'` in the first copy and `X' = S` mapping onto the second
copy. The proof of the source, which first replaces `S` by `S'`, uses (5) for the fibre over `s'`,
as stated here.

Hypothesis (5) is moved to the fibre of `X ×_S S'` over `s'` by Tag 05DC
(`AlgebraicGeometry.mem_relativeAssassin_pullback_iff`), and a point of that fibre is pinned down
by its image in `X` (`AlgebraicGeometry.pullbackLift_eq_fiberι_of_fst_eq`). -/
@[stacks 05L4]
public theorem isPureAlong_iff_relativeAssassin_specializing_mem_range_of_associatedPoints
    {X S X' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (s : S) (U : EtaleNeighborhood S s) (hU : U.IsElementary)
    (p : X' ⟶ U.scheme) [LocallyOfFiniteType p] [QuasiCompact p]
    (g : X' ⟶ X) [Etale g] (hcomm : g ≫ f = p ≫ U.toBase)
    (hflat : ∀ x : f.fiber s, IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s x))
    (hpure' : IsPureAlong
      ({ S := U.scheme
         X := X'
         f := p
         F := (Scheme.Modules.pullback g).obj F
         isFiniteType := SheafOfModules.pullback_isFiniteType g.toLRSHom.toShHom F
         isQuasicoherent := by
           have hF : F.IsQuasicoherent := inferInstance
           exact @SheafOfModules.modulePullback_isQuasicoherent X'.toRingedSpace
             X.toRingedSpace g.toLRSHom.toShHom F hF
         s := U.point } : PrePureSituation.{u}))
    (hass : ∀ z : f.fiber s,
      z ∈ Stacks.Divisors.associatedPoints ((Scheme.Modules.pullback (f.fiberι s)).obj F) →
        f.fiberι s z ∈ g '' (p ⁻¹' {U.point})) :
    IsPureAlong ({ S := S, X := X, f := f, F := F, s := s } : PrePureSituation.{u}) ↔
      ∀ x : pullback (C := Scheme.{u}) f U.toBase,
        x ∈ Stacks.Divisors.relativeAssassin (pullback.snd f U.toBase)
            ((Scheme.Modules.pullback (pullback.fst f U.toBase)).obj F) →
          pullback.snd f U.toBase x ⤳ U.point →
            x ∈ Set.range (pullback.lift g p hcomm) := by
  refine isPureAlong_iff_relativeAssassin_specializing_mem_range f F s U hU p g hcomm hflat
    hpure' ?_
  intro z hz
  set x := (pullback.snd f U.toBase).fiberι U.point z with hx
  have hrel : x ∈ Stacks.Divisors.relativeAssassin (pullback.snd f U.toBase)
      ((Scheme.Modules.pullback (pullback.fst f U.toBase)).obj F) :=
    (Stacks.Divisors.mem_relativeAssassin _ _ _).mpr ⟨U.point, z, hz, rfl⟩
  obtain ⟨s₀, w, hw, hwx⟩ := (Stacks.Divisors.mem_relativeAssassin f F _).mp
    ((mem_relativeAssassin_pullback_iff f U.toBase F x).mp hrel).1
  have hxs : f (pullback.fst f U.toBase x) = s :=
    (apply_fst_fiberι_pullback f U.toBase U.point z).trans U.map_point
  have hs₀ : s₀ = s := by
    have h := f.apply_fiberι s₀ w
    rw [hwx] at h
    exact h.symm.trans hxs
  subst s₀
  obtain ⟨y, hy, hgy⟩ := hass w hw
  exact ⟨y, pullbackLift_eq_fiberι_of_fst_eq f U hU p g hcomm z y hy (hgy.trans hwx)⟩

end AlgebraicGeometry

end
