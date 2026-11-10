module

public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalkAmplitude
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.DerivedPullback
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalk
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.Tor.IndependenceFlatModule
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tor amplitude over the base, and Tor-independent base change

Let `f : X ⟶ S` be a morphism of schemes. An object `E` of `D(𝒪_X)` has *Tor amplitude in
`[a,b]` over `S`* when, at every point `x` of `X`, the stalk complex of a representative of `E`
has Tor amplitude in `[a,b]` as a complex of modules over the local ring `𝒪_{S,f(x)}`. This is
the stalkwise reading of Tor amplitude as a complex of `f⁻¹𝒪_S`-modules.

For a cartesian square of schemes whose two morphisms to the base are Tor independent, derived
pullback preserves Tor amplitude over the base, and the derived pullback of an `𝒪_X`-module flat
over the base is its ordinary pullback.

## Main definitions

* `AlgebraicGeometry.relativeStalkComplex`: the stalk complex of a complex of `𝒪_X`-modules at a
  point, read as a complex of modules over the local ring of the base.
* `AlgebraicGeometry.HasTorAmplitudeOver`: Tor amplitude over the base.

## Main results

* `AlgebraicGeometry.derivedPullback_hasTorAmplitudeOver`: Tor amplitude over the base is
  preserved by a Tor-independent base change.
* `AlgebraicGeometry.derivedPullbackComparison_isIso_of_isFlatOver`: for a module flat over the
  base, the canonical comparison from its derived pullback to its ordinary pullback is an
  isomorphism.
* `AlgebraicGeometry.isIso_of_forall_modulesStalk` and
  `AlgebraicGeometry.quasiIso_of_forall_modulesStalk`: isomorphy and quasi-isomorphy of
  morphisms of `𝒪_X`-modules are detected on the stalks read over the local rings.

## Implementation notes

Tor amplitude of a single stalk complex is `StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift`,
the canonical Tor amplitude of the lift of the complex to the next module universe; that is the
form in which the ring-level transfer across a Tor-independent square of local rings is stated,
and `AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_moduleLift` and
`..._of_moduleLift` pass between it and the one-universe statement.

The predicate asks for *some* complex representing `E` whose stalk complexes have the bound;
`relativeStalkAmplitude_of_derivedIso` shows this does not depend on the representative, since
the stalk functor and restriction of scalars are both exact and therefore descend to the derived
categories compatibly with `DerivedCategory.Q`.

The proof of the base-change statement replaces the given representative by a K-flat one, on
which derived pullback is degreewise pullback
(`Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat`)
and whose stalk complexes are K-flat over the local rings
(`AlgebraicGeometry.kFlat_modulesStalkFunctor`). At a point `x'` upstairs the stalk of the
degreewise pullback is the extension of scalars of the stalk downstairs along the germ map
(`Stacks.ModuleSkyscraper.pullbackStalkIso`, Stacks 0098), and the ring-level transfer across the
square of local rings is
`AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_stalk_of_cartesian`.

For a module flat over the base the same K-flat resolution is used, and the content is that it
stays a resolution after pullback: that is checked at the stalks, where it is
`RingTheory.TorIndependence.quasiIso_extendScalars_of_flat_of_flat`, with the flat `T`-algebra
supplied by `AlgebraicGeometry.BaseChangeStalk.cartesian_stalk_tensor_flat`. Invertibility of
the comparison then propagates from the resolution to the module.

## References

* [Stacks Project, Tag 0C0V](https://stacks.math.columbia.edu/tag/0C0V)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open StacksDraft.TorAmplitude
open AlgebraicGeometry.BaseChangeTorAmplitude

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- The stalk at `x` of a complex of `𝒪_X`-modules, read degreewise as a complex of modules over
the local ring of the base at `f(x)` along the germ map of `f`. -/
public noncomputable def relativeStalkComplex {X S : Scheme.{u}} (f : X ⟶ S)
    (K : CochainComplex X.Modules ℤ) (x : X) :
    CochainComplex (ModuleCat.{u} (S.presheaf.stalk (f.base x))) ℤ :=
  ((ModuleCat.restrictScalars (f.stalkMap x).hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K)

/-- **Tor amplitude in `[a,b]` over the base.** An object of `D(𝒪_X)` has Tor amplitude in
`[a,b]` relative to `f : X ⟶ S` when it is represented by a complex all of whose stalk
complexes, viewed over the local rings of `S`, have Tor amplitude in `[a,b]`. -/
public def HasTorAmplitudeOver {X S : Scheme.{u}} (f : X ⟶ S)
    (E : DerivedCategory X.Modules) (a b : ℤ) : Prop :=
  ∃ K : CochainComplex X.Modules ℤ,
    Nonempty (DerivedCategory.Q.obj K ≅ E) ∧
      ∀ x : X, HasTorAmplitudeCanonicalLift.{u, u, u}
        (DerivedCategory.Q.obj (relativeStalkComplex f K x)) a b

/-- Tor amplitude over the base is a property of the isomorphism class: the representing complex
is unchanged and its comparison isomorphism is composed with the given one. -/
public theorem hasTorAmplitudeOver_of_iso {X S : Scheme.{u}} {f : X ⟶ S}
    {E E' : DerivedCategory X.Modules} (e : E ≅ E') (a b : ℤ)
    (hE : HasTorAmplitudeOver f E a b) : HasTorAmplitudeOver f E' a b := by
  obtain ⟨K, ⟨eK⟩, hK⟩ := hE
  exact ⟨K, ⟨eK ≪≫ e⟩, hK⟩

/-- Restriction of scalars along the germ map of `f` is exact, so it descends to the derived
categories compatibly with `DerivedCategory.Q`: the relative stalk complex of `K` at `x` is the
restriction of scalars of the stalk complex of `K` at `x`. -/
public noncomputable def relativeStalkRestrictIso {X S : Scheme.{u}} (f : X ⟶ S)
    (K : CochainComplex X.Modules ℤ) (x : X) :
    DerivedCategory.Q.obj (relativeStalkComplex f K x) ≅
      (ModuleCat.restrictScalars (f.stalkMap x).hom).mapDerivedCategory.obj
        (DerivedCategory.Q.obj
          (((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)) :=
  ((ModuleCat.restrictScalars (f.stalkMap x).hom).mapDerivedCategoryFactors.app
    (((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K)).symm

/-- The image of `relativeStalkComplex f K x` in the derived category is the value at
`DerivedCategory.Q.obj K` of the derived functor induced by the stalk functor followed by
restriction of scalars. Both functors are exact, so each descends to derived categories
compatibly with `DerivedCategory.Q`. -/
public noncomputable def relativeStalkComplexDerivedIso {X S : Scheme.{u}} (f : X ⟶ S)
    (K : CochainComplex X.Modules ℤ) (x : X) :
    DerivedCategory.Q.obj (relativeStalkComplex f K x) ≅
      (ModuleCat.restrictScalars (f.stalkMap x).hom).mapDerivedCategory.obj
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategory.obj
          (DerivedCategory.Q.obj K)) :=
  relativeStalkRestrictIso f K x ≪≫
    (ModuleCat.restrictScalars (f.stalkMap x).hom).mapDerivedCategory.mapIso
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategoryFactors.app K).symm

/-- Tor amplitude of the relative stalk complexes does not depend on the complex chosen to
represent an object of `D(𝒪_X)`. -/
public theorem relativeStalkAmplitude_of_derivedIso {X S : Scheme.{u}} (f : X ⟶ S) (a b : ℤ)
    {K₀ K : CochainComplex X.Modules ℤ}
    (e : DerivedCategory.Q.obj K₀ ≅ DerivedCategory.Q.obj K)
    (hK₀ : ∀ x : X, HasTorAmplitudeCanonicalLift.{u, u, u}
      (DerivedCategory.Q.obj (relativeStalkComplex f K₀ x)) a b) :
    ∀ x : X, HasTorAmplitudeCanonicalLift.{u, u, u}
      (DerivedCategory.Q.obj (relativeStalkComplex f K x)) a b := by
  intro x
  refine hasTorAmplitudeCanonical_of_iso
    ((moduleLift.{u, u, u} (S.presheaf.stalk (f.base x))).mapDerivedCategory.mapIso
      (relativeStalkComplexDerivedIso f K₀ x ≪≫
        (ModuleCat.restrictScalars (f.stalkMap x).hom).mapDerivedCategory.mapIso
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategory.mapIso e) ≪≫
        (relativeStalkComplexDerivedIso f K x).symm)) a b (hK₀ x)

/-- **Stacks 0098 degreewise, in the local-ring spelling.** Taking a complex of `𝒪_X`-modules
degreewise to its pullback along `g' : X' ⟶ X` and then to its stalk complex at `x'` is taking
its stalk complex at `g'(x')` and then extending scalars along the germ map of `g'`. -/
public noncomputable def pullbackRelativeStalkComplexIso {X' X : Scheme.{u}} (g' : X' ⟶ X)
    (x' : X') :
    (Scheme.Modules.pullback g').mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (Stacks.ModuleSkyscraper.modulesStalkFunctor X' x').mapHomologicalComplex
          (ComplexShape.up ℤ) ≅
      (Stacks.ModuleSkyscraper.modulesStalkFunctor X (g'.base x')).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        (ModuleCat.extendScalars (g'.stalkMap x').hom).mapHomologicalComplex
          (ComplexShape.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ) ≪≫
    NatIso.mapHomologicalComplex (Stacks.ModuleSkyscraper.pullbackStalkIso g' x').symm
      (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).symm

/-- `pullbackRelativeStalkComplexIso` evaluated at a complex. -/
public noncomputable def pullbackRelativeStalkObjIso {X' X : Scheme.{u}} (g' : X' ⟶ X)
    (x' : X') (K : CochainComplex X.Modules ℤ) :
    ((Stacks.ModuleSkyscraper.modulesStalkFunctor X' x').mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((Scheme.Modules.pullback g').mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      ((ModuleCat.extendScalars (g'.stalkMap x').hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((Stacks.ModuleSkyscraper.modulesStalkFunctor X (g'.base x')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) :=
  (pullbackRelativeStalkComplexIso g' x').app K

/-- At a point of the upper-left corner of a Tor-independent cartesian square, the relative stalk
complex of the degreewise pullback of a K-flat complex inherits the Tor amplitude of the relative
stalk complex downstairs. -/
public theorem relativeStalkAmplitude_pullback_of_kFlat
    {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    (f : X ⟶ S) (g : S' ⟶ S) (hpb : IsPullback g' f' f g)
    (htor : TorIndependent f g) (K : CochainComplex X.Modules ℤ) (a b : ℤ) (x' : X')
    (hK : CochainComplex.KFlat
      (((Stacks.ModuleSkyscraper.modulesStalkFunctor X (g'.base x')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K))
    (hamp : HasTorAmplitudeCanonicalLift.{u, u, u}
      (DerivedCategory.Q.obj (relativeStalkComplex f K (g'.base x'))) a b) :
    HasTorAmplitudeCanonicalLift.{u, u, u}
      (DerivedCategory.Q.obj (relativeStalkComplex f'
        (((Scheme.Modules.pullback g').mapHomologicalComplex (ComplexShape.up ℤ)).obj K) x'))
      a b := by
  have hdown := hasTorAmplitudeCanonical_of_iso
    (relativeStalkRestrictIso f K (g'.base x'))
    a b (hasTorAmplitudeCanonical_of_moduleLift _ a b hamp)
  have hup := hasTorAmplitudeCanonical_stalk_of_cartesian g' f' f g hpb htor x'
    (((Stacks.ModuleSkyscraper.modulesStalkFunctor X (g'.base x')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K) hK a b hdown
  exact hasTorAmplitudeCanonical_moduleLift _ a b (hasTorAmplitudeCanonical_of_iso
    (DerivedCategory.Q.mapIso
      (((ModuleCat.restrictScalars (f'.stalkMap x').hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).mapIso
        (pullbackRelativeStalkObjIso g' x' K).symm)) a b hup)

/-- **Stacks 0C0V (1).** For a cartesian square of schemes whose two morphisms to the base are
Tor independent, derived pullback preserves Tor amplitude over the base. -/
@[stacks 0C0V "preservation of Tor amplitude over the base",
  sga "6 III 3.5.2",
  sga "6 III 4.7.2" "amplitude inclusion"]
public theorem derivedPullback_hasTorAmplitudeOver
    {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    (f : X ⟶ S) (g : S' ⟶ S) (hpb : IsPullback g' f' f g)
    (htor : TorIndependent f g) (E : DerivedCategory X.Modules) (a b : ℤ)
    (hE : HasTorAmplitudeOver f E a b) :
    HasTorAmplitudeOver f'
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        g'.toLRSHom.toShHom).obj E) a b := by
  obtain ⟨K₀, ⟨e₀⟩, hK₀⟩ := hE
  obtain ⟨K, q, hK, -, hq, -⟩ :=
    Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution X.toSheafedSpace K₀
  have : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hq
  let eK : DerivedCategory.Q.obj K ≅ E := asIso (DerivedCategory.Q.map q) ≪≫ e₀
  refine ⟨((Scheme.Modules.pullback g').mapHomologicalComplex (ComplexShape.up ℤ)).obj K,
    ⟨(Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat g'.toLRSHom.toShHom K hK).symm ≪≫
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        g'.toLRSHom.toShHom).mapIso eK⟩, fun x' => ?_⟩
  exact relativeStalkAmplitude_pullback_of_kFlat g' f' f g hpb htor K a b x'
    (kFlat_modulesStalkFunctor (g'.base x') K hK)
    (relativeStalkAmplitude_of_derivedIso f a b (e₀ ≪≫ eK.symm) hK₀ (g'.base x'))

/-! ### Derived pullback of a module flat over the base -/

/-- The second leg of a composite is invertible as soon as the first leg and a morphism equal to
the composite are. -/
private theorem isIso_right_of_eq {C : Type*} [Category C] {W X Y : C}
    {a : W ⟶ X} {b : X ⟶ Y} {u : W ⟶ Y} (h : a ≫ b = u) (ha : IsIso a) (hu : IsIso u) :
    IsIso b := by
  have : IsIso (a ≫ b) := by rwa [h]
  exact IsIso.of_isIso_comp_left a b

/-- The first leg of a composite of morphisms of complexes is a quasi-isomorphism as soon as the
second leg and a morphism equal to the composite are. -/
private theorem quasiIso_left_of_eq {A : Type*} [Category A] [Abelian A] {ι : Type*}
    {c : ComplexShape ι} {K L M : HomologicalComplex A c}
    {t : K ⟶ L} {e : L ⟶ M} {u : K ⟶ M} (h : t ≫ e = u) (he : QuasiIso e) (hu : QuasiIso u) :
    QuasiIso t := by
  have : QuasiIso (t ≫ e) := by rwa [h]
  exact quasiIso_of_comp_right t e

/-- Isomorphy of morphisms of `𝒪_X`-modules is detected on the stalks read over the local
rings: the underlying map of abelian groups is the same as for the stalk functor over the
`RingCat`-valued stalk of the sheaf of rings. -/
public theorem isIso_of_forall_modulesStalk {X : Scheme.{u}} {M N : X.Modules} (q : M ⟶ N)
    (h : ∀ x : X, IsIso ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).map q)) : IsIso q := by
  refine (AlgebraicGeometry.SheafOfModules.isIso_iff_forall_isIso_stalkFunctor_map
    (structureSheafRing X.toRingedSpace) q).2 (fun x => ?_)
  rw [ConcreteCategory.isIso_iff_bijective]
  exact (ConcreteCategory.isIso_iff_bijective
    ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).map q)).mp (h x)

/-- Quasi-isomorphy of a morphism of complexes of `𝒪_X`-modules is detected on the stalk
complexes read over the local rings. The stalk functor is exact, so it commutes with homology,
and isomorphy of the homology maps is detected on stalks. -/
public theorem quasiIso_of_forall_modulesStalk {X : Scheme.{u}}
    {K L : CochainComplex X.Modules ℤ} (q : K ⟶ L)
    (h : ∀ x : X, QuasiIso (((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapHomologicalComplex
      (ComplexShape.up ℤ)).map q)) :
    QuasiIso q := by
  constructor
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply isIso_of_forall_modulesStalk
  intro x
  have hleft : IsIso (ShortComplex.homologyMap
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapShortComplex.map
        ((HomologicalComplex.shortComplexFunctor X.Modules (ComplexShape.up ℤ) n).map q))) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 ((h x).quasiIsoAt n)
  have hnat := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor X.Modules (ComplexShape.up ℤ) n).map q)
    (Stacks.ModuleSkyscraper.modulesStalkFunctor X x)
  exact isIso_right_of_eq hnat.symm (Iso.isIso_hom _)
    (IsIso.comp_isIso' hleft (Iso.isIso_hom _))

/-- An `𝒪_X`-module flat over `S` at `x` has flat stalk at `x` over the local ring of `S`:
`IsFlatOverAt` is exactly flatness of `relativeStalkComplex`'s degree-zero module. -/
public theorem flat_modulesStalk_of_isFlatOverAt {X S : Scheme.{u}} (f : X ⟶ S) (G : X.Modules)
    (x : X) (hG : IsFlatOverAt f.toLRSHom.toShHom G x) :
    Module.Flat (S.presheaf.stalk (f.base x))
      ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj G)) := hG

/-- **The stalkwise input to Stacks 0C0V (2).** For a Tor-independent cartesian square and an
`𝒪_X`-module `G` flat over `S`, degreewise pullback along `g'` carries a quasi-isomorphism from a
K-flat complex onto `G` to a quasi-isomorphism. -/
public theorem pullback_quasiIso_of_isFlatOver
    {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    (f : X ⟶ S) (g : S' ⟶ S) (hpb : IsPullback g' f' f g)
    (htor : TorIndependent f g) (G : X.Modules) (hG : IsFlatOver f.toLRSHom.toShHom G)
    (K : CochainComplex X.Modules ℤ)
    (hK : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex X.toSheafedSpace K)
    (q : K ⟶ (CochainComplex.singleFunctor X.Modules 0).obj G) (hq : QuasiIso q) :
    QuasiIso (((Scheme.Modules.pullback g').mapHomologicalComplex (ComplexShape.up ℤ)).map q)
    := by
  apply quasiIso_of_forall_modulesStalk
  intro x'
  set y := g'.base x' with hy
  let R := S.presheaf.stalk (f.base y)
  let A := X.presheaf.stalk y
  let B := S'.presheaf.stalk (f'.base x')
  let C := X'.presheaf.stalk x'
  have hxy : f.base y = g.base (f'.base x') :=
    congrArg (fun k : X' ⟶ S => k.base x') hpb.w
  let : Algebra R A := (f.stalkMap y).hom.toAlgebra
  let : Algebra R B :=
    (eqToHom (congrArg (fun z => S.presheaf.stalk z) hxy) ≫ g.stalkMap (f'.base x')).hom.toAlgebra
  let T := TensorProduct R A B
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower R B T := Algebra.TensorProduct.right_isScalarTower
  have : Algebra.IsPushout R A B T := TensorProduct.isPushout
  obtain ⟨φ, hleft, _, hflat⟩ :=
    AlgebraicGeometry.BaseChangeStalk.cartesian_stalk_tensor_flat g' f' f g hpb x'
  let : Algebra T C := φ.toAlgebra
  let : Algebra A C := (g'.stalkMap x').hom.toAlgebra
  have : IsScalarTower A T C := IsScalarTower.of_algebraMap_eq' hleft.symm
  have : Module.Flat T C := hflat
  let F := Stacks.ModuleSkyscraper.modulesStalkFunctor X y
  let E := ModuleCat.extendScalars (g'.stalkMap x').hom
  let s := (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app G
  let qL : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶
      (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (F.obj G) :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map q ≫ s.hom
  have : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map q) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology q F
  have : QuasiIso qL := inferInstanceAs (QuasiIso (_ ≫ _))
  have hring : QuasiIso ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map qL) :=
    RingTheory.TorIndependence.quasiIso_extendScalars_of_flat_of_flat (T := T) (C := C)
      (ringTorIndependent_of_schemeTorIndependent_stalks htor y (f'.base x') hxy)
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
      (kFlat_modulesStalkFunctor y K hK) (F.obj G)
      (flat_modulesStalk_of_isFlatOverAt f G y (hG y)) qL
  have hc : QuasiIso ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map q) ≫
      (E.mapHomologicalComplex (ComplexShape.up ℤ)).map s.hom) := by
    simpa only [qL, Functor.map_comp] using hring
  have hright : QuasiIso ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map q)) :=
    quasiIso_of_comp_right _ ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map s.hom)
  have hnat := (pullbackRelativeStalkComplexIso g' x').hom.naturality q
  have hR : QuasiIso ((pullbackRelativeStalkComplexIso g' x').hom.app K ≫
      (E.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map q)) :=
    inferInstanceAs (QuasiIso (_ ≫ _))
  exact quasiIso_left_of_eq hnat inferInstance hR

/-- Invertibility of the derived-pullback comparison propagates along a quasi-isomorphism whose
degreewise pullback is again a quasi-isomorphism. -/
public theorem derivedPullbackComparison_isIso_of_quasiIso
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    {K L : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ} (q : K ⟶ L)
    (hq : QuasiIso q)
    (hpq : QuasiIso (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map q))
    (hcK : IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
      f).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))) :
    IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)) := by
  let qh := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map q
  have hq₀ : IsIso (DerivedCategory.Qh.map qh) :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso _) q).mpr inferInstance
  have hpqh :
      IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy f).map qh) := by
    change IsIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map
      (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map q))
    exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso _) _).mpr inferInstance
  have hq₁ : IsIso ((DerivedCategory.Qh ⋙
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map qh) := by
    change IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
      (DerivedCategory.Qh.map qh))
    infer_instance
  have hn :=
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).naturality qh
  have hcomp : IsIso ((DerivedCategory.Qh ⋙
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map qh ≫
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_left ((DerivedCategory.Qh ⋙
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map qh) _

/-- **Stacks 0C0V (2).** For a Tor-independent cartesian square of schemes and an `𝒪_X`-module
`G` flat over `S`, the canonical comparison from the derived pullback of `G` along `g'` to its
ordinary pullback is an isomorphism. -/
@[stacks 0C0V "derived pullback of a module flat over the base is the ordinary pullback"]
public theorem derivedPullbackComparison_isIso_of_isFlatOver
    {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    (f : X ⟶ S) (g : S' ⟶ S) (hpb : IsPullback g' f' f g)
    (htor : TorIndependent f g) (G : X.Modules) (hG : IsFlatOver f.toLRSHom.toShHom G) :
    IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
      g'.toLRSHom.toShHom).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor X.Modules 0).obj G))) := by
  obtain ⟨K, q, hK, -, hq, -⟩ := Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution
    X.toSheafedSpace ((CochainComplex.singleFunctor X.Modules 0).obj G)
  exact derivedPullbackComparison_isIso_of_quasiIso g'.toLRSHom.toShHom q hq
    (pullback_quasiIso_of_isFlatOver g' f' f g hpb htor G hG K hK q hq)
    (Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat
      g'.toLRSHom.toShHom K hK)

end AlgebraicGeometry

end
