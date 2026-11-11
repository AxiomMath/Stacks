module

public import Mathlib.Topology.Sheaves.Functors
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialsRepresentable
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# The comparison map of differentials for a diagram of ringed spaces

Let
```
  X' --f--> X
  |         |
  h'        h
  v         v
  S' --g--> S
```
be a commutative diagram of morphisms of ringed spaces. This file constructs the canonical
map `c : f^* Ω_{X/S} ⟶ Ω_{X'/S'}` of sheaves of `𝒪_{X'}`-modules, shows that it is the
unique map carrying the pullback of the differential `d a` of a local section `a` of `𝒪_X`
to `d (f^♯ a)`, and proves that the construction is compatible with identities and with the
vertical composition of two such diagrams.

## Main definitions

* `inverseImageSheaf` and `inverseImageStructureMap` are `h⁻¹ 𝒪_S` and the structure map
  `h⁻¹ 𝒪_S ⟶ 𝒪_X` obtained from `h^♯` by adjunction.
* `SDerivation h F` is `Der_S(𝒪_X, F)`, the `S`-derivations of `h : X ⟶ S` with values in
  a sheaf of `𝒪_X`-modules `F`, namely the derivations of `𝒪_X` relative to `h⁻¹ 𝒪_S`.
* `moduleOfDifferentials h` is `Ω_{X/S}`, the differentials of `𝒪_X` relative to
  `h⁻¹ 𝒪_S`, with universal derivation `universalDerivation h`.
* `pushforwardDerivation` is the derivation `a ↦ d (f^♯ a)` of `𝒪_X` over `h⁻¹ 𝒪_S` with
  values in `f_* Ω_{X'/S'}`, and `pushforwardDifferentialMap` is the morphism
  `Ω_{X/S} ⟶ f_* Ω_{X'/S'}` it induces.
* `differentialMap` is the comparison map `f^* Ω_{X/S} ⟶ Ω_{X'/S'}`, the morphism adjoint
  to `pushforwardDifferentialMap`.
* `IsDifferentialMap` is the characterizing property of `differentialMap`.
* `modulePullbackComparison` is the canonical map
  `(f' ≫ f)^* M ⟶ f'^* (f^* M)` through which the composition law is stated.

## Main results

* `exists_inverseImageComparison`: the composite `h⁻¹ 𝒪_S ⟶ 𝒪_X ⟶ f_* 𝒪_{X'}` factors
  through `f_* (h'⁻¹ 𝒪_{S'})`.
* `differentialMap_isDifferentialMap` is the characterizing equation on local sections and
  `differentialMap_unique` says it determines the map; `existsUnique_differentialMap`
  packages the two.
* `differentialMap_id` and `pushforwardDifferentialMap_id` are the identity law,
  `differentialMap_comp` and `pushforwardDifferentialMap_comp` the composition law.

## Implementation notes

The relative differentials are those of the morphism of sheaves of commutative rings
`h⁻¹ 𝒪_S ⟶ 𝒪_X` on the site `Opens X`, so the universal property is the one proved in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialsRepresentable`. The comparison map is
produced on the adjoint side: by `RingedSpaceModuleAdjunction.homEquiv` a map
`f^* Ω_{X/S} ⟶ Ω_{X'/S'}` is the same as a map `Ω_{X/S} ⟶ f_* Ω_{X'/S'}`, and the latter is
obtained from the universal property applied to the derivation `a ↦ d (f^♯ a)`. Pushforward of
sheaves of modules already restricts scalars along `f^♯`, which is exactly the module structure
that derivation needs.

The functoriality statements come in two forms. On the pushforward side `modulePushforward`
is strictly functorial — `(f' ≫ f)_* = f_* ∘ f'_*` and `(𝟙 X)_* = 𝟭` hold by `rfl` — so
`pushforwardDifferentialMap_id` and `pushforwardDifferentialMap_comp` are equalities with no
comparison maps in them. Pullback is only defined as a left adjoint, so on the pullback side
the identity law identifies `differentialMap` with the counit of the adjunction and the
composition law inserts `modulePullbackComparison`, the mate of the identity
`(f' ≫ f)_* = f_* ∘ f'_*`.

Everything is at `RingedSpace.{u, u}` with `SheafOfModules.{u}`; see the module docstring of
`StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace` for why that is forced.

## References

* [Stacks Project, Tag 08RU](https://stacks.math.columbia.edu/tag/08RU)
* [Stacks Project, Tag 01UW](https://stacks.math.columbia.edu/tag/01UW), the composition law.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Sheaves.RingedSpaceDifferentials

variable {X'' X' X S'' S' S : RingedSpace.{u, u}}

/-- The adjunction `f⁻¹ ⊣ f_*` between sheaves of commutative rings on the two spaces
underlying a morphism of ringed spaces. -/
noncomputable abbrev sheafAdjunction (f : X' ⟶ X) :
    TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base ⊣
      TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base :=
  TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base

/-- The component `f^♯ : 𝒪_X ⟶ f_* 𝒪_{X'}` of a morphism of ringed spaces, read as a
morphism of sheaves of commutative rings on `X`. -/
noncomputable def structureSheafMap (f : X' ⟶ X) :
    X.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X'.sheaf :=
  ⟨f.hom.c⟩

/-- The structure-sheaf component of a composite of morphisms of ringed spaces. -/
theorem structureSheafMap_comp (f : X' ⟶ X) (h : X ⟶ S) :
    structureSheafMap (f ≫ h) = structureSheafMap h ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} h.hom.base).map (structureSheafMap f) :=
  rfl

/-- The inverse image `h⁻¹ 𝒪_S` of the structure sheaf of `S` along a morphism of ringed
spaces `h : X ⟶ S`, a sheaf of commutative rings on `X`. -/
noncomputable abbrev inverseImageSheaf (h : X ⟶ S) : TopCat.Sheaf CommRingCat.{u} X.carrier :=
  (TopCat.Sheaf.pullback CommRingCat.{u} h.hom.base).obj S.sheaf

/-- The structure map `h⁻¹ 𝒪_S ⟶ 𝒪_X` of a morphism of ringed spaces `h : X ⟶ S`: the
morphism adjoint to `h^♯` under `h⁻¹ ⊣ h_*`. -/
noncomputable def inverseImageStructureMap (h : X ⟶ S) : inverseImageSheaf h ⟶ X.sheaf :=
  ((sheafAdjunction h).homEquiv S.sheaf X.sheaf).symm (structureSheafMap h)

/-- `h^♯` is recovered from `h⁻¹ 𝒪_S ⟶ 𝒪_X` by adjunction. -/
theorem homEquiv_inverseImageStructureMap (h : X ⟶ S) :
    (sheafAdjunction h).homEquiv S.sheaf X.sheaf (inverseImageStructureMap h)
      = structureSheafMap h :=
  Equiv.apply_symm_apply _ _

/-- The unit of `h⁻¹ ⊣ h_*` followed by `h_*` of the structure map is `h^♯`. -/
private theorem unit_comp_map_inverseImageStructureMap (h : X ⟶ S) :
    (sheafAdjunction h).unit.app S.sheaf ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} h.hom.base).map (inverseImageStructureMap h)
      = structureSheafMap h :=
  (Adjunction.homEquiv_unit (sheafAdjunction h) S.sheaf X.sheaf
    (inverseImageStructureMap h)).symm.trans (homEquiv_inverseImageStructureMap h)

/-- Transport of a factorization of the structure-sheaf component of `f ≫ h` along an
equality of morphisms of ringed spaces, with the two pushforwards in the conclusion separated. -/
private theorem exists_factorization_of_eq (f : X' ⟶ X) (h : X ⟶ S) {m : X' ⟶ S}
    (e : f ≫ h = m) {N : TopCat.Sheaf CommRingCat.{u} X'.carrier} (α : N ⟶ X'.sheaf)
    (β : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} m.hom.base).obj N)
    (hβ : β ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} m.hom.base).map α
      = structureSheafMap m) :
    ∃ γ : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} h.hom.base).obj
        ((TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj N),
      γ ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} h.hom.base).map
          ((TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map α)
        = structureSheafMap h ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} h.hom.base).map
          (structureSheafMap f) := by
  subst e
  exact ⟨β, hβ⟩

/-- For a commutative diagram of morphisms of ringed spaces the composite
`h⁻¹ 𝒪_S ⟶ 𝒪_X ⟶ f_* 𝒪_{X'}` factors through `f_* (h'⁻¹ 𝒪_{S'})`. -/
theorem exists_inverseImageComparison (f : X' ⟶ X) (h : X ⟶ S) (h' : X' ⟶ S') (g : S' ⟶ S)
    (hcomm : f ≫ h = h' ≫ g) :
    ∃ ψ : inverseImageSheaf h ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj (inverseImageSheaf h'),
      inverseImageStructureMap h ≫ structureSheafMap f
        = ψ ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
            (inverseImageStructureMap h') := by
  have hβ : (structureSheafMap g ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map
        ((sheafAdjunction h').unit.app S'.sheaf)) ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map
        ((TopCat.Sheaf.pushforward CommRingCat.{u} h'.hom.base).map
          (inverseImageStructureMap h'))
      = structureSheafMap g ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map
        (structureSheafMap h') := by
    rw [Category.assoc, ← Functor.map_comp,
      unit_comp_map_inverseImageStructureMap h']
  obtain ⟨γ, hγ⟩ := exists_factorization_of_eq f h hcomm (inverseImageStructureMap h') _ hβ
  refine ⟨((sheafAdjunction h).homEquiv S.sheaf _).symm γ, ?_⟩
  apply ((sheafAdjunction h).homEquiv S.sheaf _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right,
    homEquiv_inverseImageStructureMap, Equiv.apply_symm_apply]
  exact hγ.symm

/-- `Der_S(𝒪_X, F)`, the type of *`S`-derivations* of a morphism of ringed spaces
`h : X ⟶ S` with values in a sheaf of `𝒪_X`-modules `F`: a derivation of `𝒪_X` relative to
`h⁻¹ 𝒪_S`, that is, an `inverseImageStructureMap h`-derivation in the sense of Tag 01UN. -/
@[stacks 08RT "S-derivations into an O_X-module: the set Der_S(O_X, F)",
  ega "IV 16.5.1",
  sga "3 VIIA 1.2.0" "more general"]
noncomputable abbrev SDerivation (h : X ⟶ S)
    (F : SheafOfModules.{u} (structureSheafRing X)) :=
  Differentials.SheafDerivation (C := Opens X.carrier) (inverseImageSheaf h) X.sheaf
    (inverseImageStructureMap h) F

/-- The sheaf of relative differentials `Ω_{X/S}` of a morphism of ringed spaces `h : X ⟶ S`:
the sheaf of differentials of `𝒪_X` relative to `h⁻¹ 𝒪_S`. -/
@[stacks 08RT "the sheaf of differentials Omega_{X/S} of X over S"]
noncomputable def moduleOfDifferentials (h : X ⟶ S) :
    SheafOfModules.{u} (structureSheafRing X) :=
  Differentials.moduleOfDifferentials (inverseImageSheaf h) X.sheaf (inverseImageStructureMap h)

/-- The universal relative derivation `d_{X/S} : 𝒪_X ⟶ Ω_{X/S}`. -/
@[stacks 08RT "the universal S-derivation d_{X/S} with which Omega_{X/S} is endowed"]
noncomputable def universalDerivation (h : X ⟶ S) :
    SDerivation h (moduleOfDifferentials h) :=
  Differentials.universalDerivation (inverseImageSheaf h) X.sheaf (inverseImageStructureMap h)

/-- `RingedSpaceModuleAdjunction.homEquiv` is the hom-set bijection of the adjunction
`f^* ⊣ f_*`. -/
theorem homEquiv_eq (f : X' ⟶ X) (F : SheafOfModules.{u} (structureSheafRing X'))
    (G : SheafOfModules.{u} (structureSheafRing X)) :
    RingedSpaceModuleAdjunction.homEquiv f F G
      = (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f).homEquiv G F :=
  rfl

/-- Evaluating a composite of morphisms of sheaves of modules on a local section. -/
private theorem comp_val_app_hom_apply {X : RingedSpace.{u, u}}
    {A B C : SheafOfModules.{u} (structureSheafRing X)} (φ : A ⟶ B) (ψ : B ⟶ C)
    (U : (Opens X.carrier)ᵒᵖ) (x : A.val.obj U) :
    ((φ ≫ ψ).val.app U).hom x = (ψ.val.app U).hom ((φ.val.app U).hom x) :=
  rfl

section DifferentialMap

variable (f : X' ⟶ X) (h : X ⟶ S) (h' : X' ⟶ S') (g : S' ⟶ S) (hcomm : f ≫ h = h' ≫ g)

/-- For a commutative diagram of morphisms of ringed spaces, the universal derivation of
`X'` over `S'` composed with `f^♯` is a derivation of `𝒪_X` over `h⁻¹ 𝒪_S` with values in
`f_* Ω_{X'/S'}`, the latter regarded as a sheaf of `𝒪_X`-modules by restriction of scalars
along `f^♯`. -/
noncomputable def pushforwardDerivation :
    SDerivation h
      ((RingedSpaceModuleAdjunction.modulePushforward f).obj (moduleOfDifferentials h')) where
  d {U} := ((universalDerivation h').d
      (X := .op ((Opens.map f.hom.base).obj U.unop))).comp
    ((f.hom.c.app U).hom).toAddMonoidHom
  d_mul {U} a b := by
    refine Eq.trans (congrArg (fun z => (universalDerivation h').d z)
      (map_mul (f.hom.c.app U).hom a b)) ?_
    exact (universalDerivation h').d_mul _ _
  d_map {U V} i x := by
    have heq : (f.hom.c.app V).hom ((X.presheaf.map i).hom x)
        = ((f.hom.base _* X'.presheaf).map i).hom ((f.hom.c.app U).hom x) := by
      have hnn := congrArg
        (fun (t : X.presheaf.obj U ⟶ (f.hom.base _* X'.presheaf).obj V) => t.hom x)
        (f.hom.c.naturality i)
      simp only [CommRingCat.hom_comp] at hnn
      exact hnn
    refine Eq.trans (congrArg (fun z => (universalDerivation h').d z) heq) ?_
    exact (universalDerivation h').d_map _ _
  d_app {U} a := by
    obtain ⟨ψ, hψ⟩ := exists_inverseImageComparison f h h' g hcomm
    have hsq : (inverseImageStructureMap h).hom ≫ (structureSheafMap f).hom
        = ψ.hom ≫ ((TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
            (inverseImageStructureMap h')).hom := Sheaf.hom_ext_iff.mp hψ
    have hc : (f.hom.c.app U).hom (((inverseImageStructureMap h).hom.app U).hom a)
        = ((inverseImageStructureMap h').hom.app
            (.op ((Opens.map f.hom.base).obj U.unop))).hom ((ψ.hom.app U).hom a) := by
      have hnn := congrArg
        (fun (t : (inverseImageSheaf h).obj.obj U ⟶ (f.hom.base _* X'.presheaf).obj U) => t.hom a)
        (congrFun (congrArg NatTrans.app hsq) U)
      simp only [NatTrans.comp_app] at hnn
      exact hnn
    refine Eq.trans (congrArg (fun z => (universalDerivation h').d z) hc) ?_
    exact PresheafOfModulesOfCommRing.Derivation'.d_app (universalDerivation h') _

/-- The derivation `pushforwardDerivation` sends a local section `a` of `𝒪_X` to
`d (f^♯ a)`. -/
theorem pushforwardDerivation_d {U : (Opens X.carrier)ᵒᵖ} (a : X.presheaf.obj U) :
    (pushforwardDerivation f h h' g hcomm).d a
      = (universalDerivation h').d ((f.hom.c.app U).hom a) :=
  rfl

/-- The universal property of `Ω_{X/S}` applied to `pushforwardDerivation`: there is a
unique morphism `Ω_{X/S} ⟶ f_* Ω_{X'/S'}` of sheaves of `𝒪_X`-modules carrying the
universal derivation of `X` over `S` to `d ∘ f^♯`. -/
theorem existsUnique_pushforwardDifferentialMap :
    ∃! c : moduleOfDifferentials h ⟶
        (RingedSpaceModuleAdjunction.modulePushforward f).obj (moduleOfDifferentials h'),
      (universalDerivation h).postcomp c.val = pushforwardDerivation f h h' g hcomm :=
  Differentials.universalDerivation_isUniversal (inverseImageSheaf h) X.sheaf
    (inverseImageStructureMap h) _ (pushforwardDerivation f h h' g hcomm)

/-- The morphism `Ω_{X/S} ⟶ f_* Ω_{X'/S'}` adjoint to the comparison map of
differentials. -/
noncomputable def pushforwardDifferentialMap :
    moduleOfDifferentials h ⟶
      (RingedSpaceModuleAdjunction.modulePushforward f).obj (moduleOfDifferentials h') :=
  Exists.choose (existsUnique_pushforwardDifferentialMap f h h' g hcomm)

/-- `pushforwardDifferentialMap` carries the universal derivation of `X` over `S` to the
derivation `pushforwardDerivation`. -/
theorem universalDerivation_postcomp_pushforwardDifferentialMap :
    (universalDerivation h).postcomp (pushforwardDifferentialMap f h h' g hcomm).val
      = pushforwardDerivation f h h' g hcomm :=
  (Exists.choose_spec (existsUnique_pushforwardDifferentialMap f h h' g hcomm)).1

/-- The characterizing property of `pushforwardDifferentialMap` on local sections: it sends
`d a` to `d (f^♯ a)`. -/
theorem pushforwardDifferentialMap_val_app_d {U : (Opens X.carrier)ᵒᵖ} (a : X.presheaf.obj U) :
    ((pushforwardDifferentialMap f h h' g hcomm).val.app U).hom ((universalDerivation h).d a)
      = (universalDerivation h').d ((f.hom.c.app U).hom a) :=
  PresheafOfModulesOfCommRing.Derivation.congr_d
    (universalDerivation_postcomp_pushforwardDifferentialMap f h h' g hcomm) a

/-- A morphism `Ω_{X/S} ⟶ f_* Ω_{X'/S'}` sending `d a` to `d (f^♯ a)` is
`pushforwardDifferentialMap`. -/
private theorem pushforwardDifferentialMap_eq_of_d
    (c : moduleOfDifferentials h ⟶
      (RingedSpaceModuleAdjunction.modulePushforward f).obj (moduleOfDifferentials h'))
    (hc : ∀ (U : (Opens X.carrier)ᵒᵖ) (a : X.presheaf.obj U),
      (c.val.app U).hom ((universalDerivation h).d a)
        = (universalDerivation h').d ((f.hom.c.app U).hom a)) :
    pushforwardDifferentialMap f h h' g hcomm = c :=
  ((Exists.choose_spec (existsUnique_pushforwardDifferentialMap f h h' g hcomm)).2 c
    (PresheafOfModulesOfCommRing.Derivation.ext (by ext U a; exact hc U a))).symm

/-- The characterizing property of the comparison map of differentials: under the
adjunction `f^* ⊣ f_*`, the morphism `c : f^* Ω_{X/S} ⟶ Ω_{X'/S'}` carries the pullback of
the differential `d a` of a local section `a` of `𝒪_X` to the differential `d (f^♯ a)` of
its pullback. -/
def IsDifferentialMap (c : (RingedSpaceModuleAdjunction.modulePullback f).obj
    (moduleOfDifferentials h) ⟶ moduleOfDifferentials h') : Prop :=
  ∀ (U : Opens X.carrier) (a : X.presheaf.obj (.op U)),
    ((RingedSpaceModuleAdjunction.homEquiv f (moduleOfDifferentials h')
        (moduleOfDifferentials h) c).val.app (.op U)).hom ((universalDerivation h).d a)
      = (universalDerivation h').d ((f.hom.c.app (.op U)).hom a)

/-- The canonical comparison map `c : f^* Ω_{X/S} ⟶ Ω_{X'/S'}` of sheaves of `𝒪_{X'}`-modules
attached to a commutative diagram of morphisms of ringed spaces
```
  X' --f--> X
  |         |
  h'        h
  v         v
  S' --g--> S
```
It is the morphism adjoint to `pushforwardDifferentialMap`, and
`differentialMap_isDifferentialMap` together with `differentialMap_unique` say that it is
the unique morphism carrying the pullback of `d a` to `d (f^♯ a)` on local sections. -/
@[stacks 08RU "the canonical map c_f : f^*Omega_{X/S} -> Omega_{X'/S'}"]
noncomputable def differentialMap :
    (RingedSpaceModuleAdjunction.modulePullback f).obj (moduleOfDifferentials h) ⟶
      moduleOfDifferentials h' :=
  (RingedSpaceModuleAdjunction.homEquiv f (moduleOfDifferentials h')
    (moduleOfDifferentials h)).symm (pushforwardDifferentialMap f h h' g hcomm)

/-- `differentialMap` and `pushforwardDifferentialMap` correspond to one another under the
adjunction `f^* ⊣ f_*`. -/
theorem homEquiv_differentialMap :
    RingedSpaceModuleAdjunction.homEquiv f (moduleOfDifferentials h')
        (moduleOfDifferentials h) (differentialMap f h h' g hcomm)
      = pushforwardDifferentialMap f h h' g hcomm := by
  rw [differentialMap, Equiv.apply_symm_apply]

/-- The unit of `f^* ⊣ f_*` followed by `f_*` of the comparison map is the adjoint
comparison map. -/
theorem unit_comp_map_differentialMap :
    (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f).unit.app
        (moduleOfDifferentials h) ≫
      (RingedSpaceModuleAdjunction.modulePushforward f).map (differentialMap f h h' g hcomm)
      = pushforwardDifferentialMap f h h' g hcomm :=
  (Adjunction.homEquiv_unit
    (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f)
    (moduleOfDifferentials h) (moduleOfDifferentials h')
    (differentialMap f h h' g hcomm)).symm.trans (homEquiv_differentialMap f h h' g hcomm)

/-- `differentialMap` has the characterizing property: on local sections it carries the
pullback of `d a` to `d (f^♯ a)`. -/
theorem differentialMap_isDifferentialMap :
    IsDifferentialMap f h h' (differentialMap f h h' g hcomm) := by
  intro U a
  rw [differentialMap, Equiv.apply_symm_apply]
  exact PresheafOfModulesOfCommRing.Derivation.congr_d
    (universalDerivation_postcomp_pushforwardDifferentialMap f h h' g hcomm) a

/-- Uniqueness: a morphism `f^* Ω_{X/S} ⟶ Ω_{X'/S'}` with the characterizing property of
`differentialMap` is `differentialMap`. -/
theorem differentialMap_unique (c : (RingedSpaceModuleAdjunction.modulePullback f).obj
    (moduleOfDifferentials h) ⟶ moduleOfDifferentials h') (hc : IsDifferentialMap f h h' c) :
    c = differentialMap f h h' g hcomm := by
  apply (RingedSpaceModuleAdjunction.homEquiv f (moduleOfDifferentials h')
    (moduleOfDifferentials h)).injective
  rw [differentialMap, Equiv.apply_symm_apply]
  exact (pushforwardDifferentialMap_eq_of_d f h h' g hcomm _ fun U a => hc U.unop a).symm

include hcomm in
/-- **Stacks Project, Tag 08RU.** The comparison map of differentials attached to a
commutative diagram of morphisms of ringed spaces exists and is uniquely determined by its
effect on differentials of local sections. -/
theorem existsUnique_differentialMap :
    ∃! c : (RingedSpaceModuleAdjunction.modulePullback f).obj (moduleOfDifferentials h) ⟶
      moduleOfDifferentials h', IsDifferentialMap f h h' c :=
  ⟨differentialMap f h h' g hcomm, differentialMap_isDifferentialMap f h h' g hcomm,
    fun c hc ↦ differentialMap_unique f h h' g hcomm c hc⟩

end DifferentialMap

section Functoriality

/-- The canonical map `(f' ≫ f)^* M ⟶ f'^* (f^* M)`: the morphism adjoint to the composite
of the two units of `f^* ⊣ f_*` and `f'^* ⊣ f'_*`, using that
`(f' ≫ f)_* = f_* ∘ f'_*`. -/
noncomputable def modulePullbackComparison (f : X' ⟶ X) (f' : X'' ⟶ X')
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (RingedSpaceModuleAdjunction.modulePullback (f' ≫ f)).obj M ⟶
      (RingedSpaceModuleAdjunction.modulePullback f').obj
        ((RingedSpaceModuleAdjunction.modulePullback f).obj M) :=
  (RingedSpaceModuleAdjunction.homEquiv (f' ≫ f)
    ((RingedSpaceModuleAdjunction.modulePullback f').obj
      ((RingedSpaceModuleAdjunction.modulePullback f).obj M)) M).symm
    ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f).unit.app M ≫
      (RingedSpaceModuleAdjunction.modulePushforward f).map
        ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f').unit.app
          ((RingedSpaceModuleAdjunction.modulePullback f).obj M)))

/-- The adjoint description of `modulePullbackComparison`. -/
theorem homEquiv_modulePullbackComparison (f : X' ⟶ X) (f' : X'' ⟶ X')
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction (f' ≫ f)).homEquiv M
        ((RingedSpaceModuleAdjunction.modulePullback f').obj
          ((RingedSpaceModuleAdjunction.modulePullback f).obj M))
        (modulePullbackComparison f f' M)
      = (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f).unit.app M ≫
        (RingedSpaceModuleAdjunction.modulePushforward f).map
          ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f').unit.app
            ((RingedSpaceModuleAdjunction.modulePullback f).obj M)) := by
  rw [modulePullbackComparison, homEquiv_eq, Equiv.apply_symm_apply]
  rfl

/-- Functoriality, identities: the adjoint comparison map of the identity diagram of
`h : X ⟶ S` is the identity of `Ω_{X/S}`. -/
theorem pushforwardDifferentialMap_id (h : X ⟶ S) (hcomm : 𝟙 X ≫ h = h ≫ 𝟙 S) :
    pushforwardDifferentialMap (𝟙 X) h h (𝟙 S) hcomm = 𝟙 (moduleOfDifferentials h) := by
  exact pushforwardDifferentialMap_eq_of_d (𝟙 X) h h (𝟙 S) hcomm _ fun U a => rfl

/-- Functoriality, identities: the comparison map of the identity diagram of `h : X ⟶ S` is
the counit `(𝟙 X)^* Ω_{X/S} ⟶ Ω_{X/S}` of the adjunction, the canonical identification of
`(𝟙 X)^*` with the identity functor. -/
theorem differentialMap_id (h : X ⟶ S) (hcomm : 𝟙 X ≫ h = h ≫ 𝟙 S) :
    differentialMap (𝟙 X) h h (𝟙 S) hcomm
      = (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction (𝟙 X)).counit.app
          (moduleOfDifferentials h) := by
  rw [differentialMap, pushforwardDifferentialMap_id]
  exact Adjunction.homEquiv_symm_id
    (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction (𝟙 X))
    (moduleOfDifferentials h)

variable (f : X' ⟶ X) (f' : X'' ⟶ X') (h : X ⟶ S) (h' : X' ⟶ S') (h'' : X'' ⟶ S'')
  (g : S' ⟶ S) (g' : S'' ⟶ S') (hcomm : f ≫ h = h' ≫ g) (hcomm' : f' ≫ h' = h'' ≫ g')
  (hcomm'' : (f' ≫ f) ≫ h = h'' ≫ (g' ≫ g))

/-- Functoriality, composition: the adjoint comparison map of a vertical composite of two
commutative diagrams is the composite of the adjoint comparison maps. -/
theorem pushforwardDifferentialMap_comp :
    pushforwardDifferentialMap (f' ≫ f) h h'' (g' ≫ g) hcomm''
      = pushforwardDifferentialMap f h h' g hcomm ≫
        (RingedSpaceModuleAdjunction.modulePushforward f).map
          (pushforwardDifferentialMap f' h' h'' g' hcomm') := by
  refine pushforwardDifferentialMap_eq_of_d _ _ _ _ _ _ fun U a => ?_
  refine (comp_val_app_hom_apply (pushforwardDifferentialMap f h h' g hcomm)
    ((RingedSpaceModuleAdjunction.modulePushforward f).map
      (pushforwardDifferentialMap f' h' h'' g' hcomm')) U _).trans ?_
  exact (congrArg _ (pushforwardDifferentialMap_val_app_d f h h' g hcomm a)).trans
    (pushforwardDifferentialMap_val_app_d f' h' h'' g' hcomm' ((f.hom.c.app U).hom a))

/-- Functoriality, composition: the comparison map of a vertical composite of two commutative
diagrams of ringed spaces is the composite of the comparison maps, after the canonical
identification `(f' ≫ f)^* ⟶ f'^* (f^*)`. This is the relation `c_{f ∘ f'} = c_{f'} ∘ (f')^* c_f`
of Tag 01UW. -/
@[stacks 01UW]
theorem differentialMap_comp :
    differentialMap (f' ≫ f) h h'' (g' ≫ g) hcomm''
      = modulePullbackComparison f f' (moduleOfDifferentials h) ≫
        ((RingedSpaceModuleAdjunction.modulePullback f').map
            (differentialMap f h h' g hcomm) ≫ differentialMap f' h' h'' g' hcomm') := by
  have inner : (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f').unit.app
        ((RingedSpaceModuleAdjunction.modulePullback f).obj (moduleOfDifferentials h)) ≫
      (RingedSpaceModuleAdjunction.modulePushforward f').map
        ((RingedSpaceModuleAdjunction.modulePullback f').map (differentialMap f h h' g hcomm) ≫
          differentialMap f' h' h'' g' hcomm')
      = differentialMap f h h' g hcomm ≫ pushforwardDifferentialMap f' h' h'' g' hcomm' := by
    rw [Functor.map_comp, ← Category.assoc, ← Functor.comp_map,
      ← (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f').unit.naturality,
      Category.assoc, unit_comp_map_differentialMap]
    rfl
  apply (RingedSpaceModuleAdjunction.homEquiv (f' ≫ f) (moduleOfDifferentials h'')
    (moduleOfDifferentials h)).injective
  rw [homEquiv_differentialMap, pushforwardDifferentialMap_comp f f' h h' h'' g g' hcomm
      hcomm' hcomm'', homEquiv_eq, Adjunction.homEquiv_naturality_right,
    homEquiv_modulePullbackComparison, Functor.map_comp]
  change pushforwardDifferentialMap f h h' g hcomm ≫
      (RingedSpaceModuleAdjunction.modulePushforward f).map
        (pushforwardDifferentialMap f' h' h'' g' hcomm')
    = ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f).unit.app
          (moduleOfDifferentials h) ≫
        (RingedSpaceModuleAdjunction.modulePushforward f).map
          ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f').unit.app
            ((RingedSpaceModuleAdjunction.modulePullback f).obj (moduleOfDifferentials h)))) ≫
      ((RingedSpaceModuleAdjunction.modulePushforward f).map
          ((RingedSpaceModuleAdjunction.modulePushforward f').map
            ((RingedSpaceModuleAdjunction.modulePullback f').map
              (differentialMap f h h' g hcomm))) ≫
        (RingedSpaceModuleAdjunction.modulePushforward f).map
          ((RingedSpaceModuleAdjunction.modulePushforward f').map
            (differentialMap f' h' h'' g' hcomm')))
  simp only [← Functor.map_comp, Category.assoc]
  rw [inner, Functor.map_comp, ← Category.assoc, unit_comp_map_differentialMap]

end Functoriality

end Stacks.Sheaves.RingedSpaceDifferentials

end

/-!
# The transitivity sequence of differentials on ringed spaces

Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of ringed spaces. The comparison maps
`differentialMap` above, applied to the two squares
```
  X --f--> Y            X --𝟙--> X
  |        |            |        |
  f ≫ g    g           f       f ≫ g
  v        v            v        v
  S --𝟙--> S            Y --g--> S
```
give a sequence
```
  f^* Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y} ⟶ 0
```
of sheaves of `𝒪_X`-modules, and this file proves that it is exact: the second map is an
epimorphism and the sequence is exact at `Ω_{X/S}`.

## Main definitions

* `derivationConstants` is the presheaf of rings of sections annihilated by a relative
  derivation, `derivationConstantsSheaf` is it together with the sheaf condition, and
  `derivationConstantsι` / `derivationConstantsSheafι` are its inclusion into the ambient
  (pre)sheaf of rings.
* `toRelativeDifferentials f g` is the canonical map `Ω_{X/S} ⟶ Ω_{X/Y}`, the comparison map
  of the right-hand square above read through the identification of `(𝟙 X)^*` with the
  identity functor.
* `derivationOfCompEqZero` and `descOfCompEqZero` produce, from a morphism out of `Ω_{X/S}`
  annihilated by the comparison map from `f^* Ω_{Y/S}`, the relative derivation over
  `f⁻¹ 𝒪_Y` it defines and the induced morphism out of `Ω_{X/Y}`.

## Main results

* `derivation_d_inverseImageStructureMap_eq_zero`: a relative derivation of `𝒪_X` which
  annihilates `d (f^♯ b)` for every local section `b` of `𝒪_Y` annihilates the whole image of
  `f⁻¹ 𝒪_Y ⟶ 𝒪_X`, hence is a derivation over `f⁻¹ 𝒪_Y`.
* `isColimitCokernelCoforkToRelativeDifferentials` says that `Ω_{X/Y}` is a cokernel of
  `f^* Ω_{Y/S} ⟶ Ω_{X/S}`.
* `triangleDifferentials_epi` and `triangleDifferentials_exact` are Tag 0H79: the map
  `Ω_{X/S} ⟶ Ω_{X/Y}` is an epimorphism, and the two comparison maps form a short complex
  which is exact at `Ω_{X/S}`.

## Implementation notes

The `derivationConstants` construction is carried out for a derivation of an arbitrary
presheaf of commutative rings, since only the Leibniz rule and compatibility with
restriction are used; the sheaf condition is then proved on a ringed space.

Everything is stated for `RingedSpace.{u, u}` with `SheafOfModules.{u}`, matching the
comparison maps above; see the module docstring of
`StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace` for why that is forced and not
chosen.

## References

* [Stacks Project, Tag 0H79](https://stacks.math.columbia.edu/tag/0H79)
-/


@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u v w

namespace Stacks.Sheaves.RingedSpaceDifferentials

section Constants

variable {E : Type u} [Category.{w} E] {R₁ R₂ : Eᵒᵖ ⥤ CommRingCat.{v}} {ψ : R₁ ⟶ R₂}
  {M : PresheafOfModules.{v} (R₂ ⋙ forget₂ CommRingCat.{v} RingCat.{v})}
  (D : PresheafOfModulesOfCommRing.Derivation' M ψ)

/-- The subring of sections annihilated by a relative derivation. -/
def derivationConstantsSubring (U : Eᵒᵖ) : Subring (R₂.obj U) where
  carrier := {a | D.d a = 0}
  mul_mem' {a b} ha hb := by
    have h := D.d_mul a b
    rw [show D.d a = 0 from ha, show D.d b = 0 from hb, smul_zero, smul_zero, add_zero] at h
    exact h
  one_mem' := D.d_one U
  add_mem' {a b} ha hb := by
    have h := map_add D.d a b
    rw [show D.d a = 0 from ha, show D.d b = 0 from hb, add_zero] at h
    exact h
  zero_mem' := map_zero D.d
  neg_mem' {a} ha := by
    have h := map_neg D.d a
    rw [show D.d a = 0 from ha, neg_zero] at h
    exact h

/-- Membership in `derivationConstantsSubring` is being annihilated by the derivation. -/
theorem mem_derivationConstantsSubring {U : Eᵒᵖ} (a : R₂.obj U) :
    a ∈ derivationConstantsSubring D U ↔ D.d a = 0 := Iff.rfl

/-- The presheaf of commutative rings of sections annihilated by a relative derivation. -/
@[simps obj]
def derivationConstants : Eᵒᵖ ⥤ CommRingCat.{v} where
  obj U := CommRingCat.of (derivationConstantsSubring D U)
  map {U V} i := CommRingCat.ofHom
    { toFun a := ⟨(R₂.map i) a.1, by
        have h := D.d_map i a.1
        rw [show D.d a.1 = 0 from a.2, map_zero] at h
        exact h⟩
      map_one' := Subtype.ext (by simp)
      map_mul' a b := Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' a b := Subtype.ext (by simp) }
  map_id U := by
    ext a
    exact congrArg (fun g => (ConcreteCategory.hom g) a.1) (R₂.map_id U)
  map_comp {U V W} i j := by
    ext a
    exact congrArg (fun g => (ConcreteCategory.hom g) a.1) (R₂.map_comp i j)

/-- The inclusion of the presheaf of sections annihilated by a derivation. -/
@[simps]
def derivationConstantsι : derivationConstants D ⟶ R₂ where
  app U := CommRingCat.ofHom (derivationConstantsSubring D U).subtype
  naturality _ _ _ := rfl

end Constants

section Sheaf

open TopCat.Presheaf

variable {X : RingedSpace.{u, u}}
  {M : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
  (hM : TopCat.Presheaf.IsSheaf M.presheaf)
  {R₁ : (Opens X.carrier)ᵒᵖ ⥤ CommRingCat.{u}} {ψ : R₁ ⟶ X.presheaf}
  (D : PresheafOfModulesOfCommRing.Derivation' M ψ)

include hM in
/-- The sections annihilated by a relative derivation with values in a *sheaf* of modules
form a sheaf of rings. -/
theorem derivationConstants_isSheaf : TopCat.Presheaf.IsSheaf (derivationConstants D) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  have hsf' : IsCompatible X.presheaf U (fun i => (sf i).1) := fun i j =>
    congrArg Subtype.val (hsf i j)
  obtain ⟨s, hs, huniq⟩ := X.IsSheaf.isSheafUniqueGluing U (fun i => (sf i).1) hsf'
  have hD : D.d s = 0 := by
    refine TopCat.Presheaf.IsSheaf.section_ext hM ?_
    intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    refine ⟨U i, le_iSup U i, hi, ?_⟩
    have h1 := D.d_map (homOfLE (le_iSup U i)).op s
    have h2 : (X.presheaf.map (homOfLE (le_iSup U i)).op) s = (sf i).1 := hs i
    refine Eq.trans ?_ (map_zero _).symm
    exact h1.symm.trans ((congrArg D.d h2).trans (sf i).2)
  refine ⟨⟨s, hD⟩, fun i => Subtype.ext (hs i), ?_⟩
  intro t ht
  exact Subtype.ext (huniq t.1 (fun i => congrArg Subtype.val (ht i)))

end Sheaf

section Crux

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  {M : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
  (hM : TopCat.Presheaf.IsSheaf M.presheaf)
  {R₁ : (Opens X.carrier)ᵒᵖ ⥤ CommRingCat.{u}} {ψ : R₁ ⟶ X.presheaf}
  (D : PresheafOfModulesOfCommRing.Derivation' M ψ)

/-- The subsheaf of rings of `𝒪_X` of sections annihilated by a relative derivation with
values in a sheaf of modules. -/
def derivationConstantsSheaf : TopCat.Sheaf CommRingCat.{u} X.carrier :=
  ⟨derivationConstants D, derivationConstants_isSheaf hM D⟩

/-- The inclusion `derivationConstantsSheaf ⟶ 𝒪_X`. -/
def derivationConstantsSheafι : derivationConstantsSheaf hM D ⟶ X.sheaf :=
  ObjectProperty.homMk (derivationConstantsι D)

/-- If a relative derivation of `𝒪_X` annihilates `d (f^♯ b)` for every local section `b` of
`𝒪_Y`, then `f^♯ : 𝒪_Y ⟶ f_* 𝒪_X` factors through the pushforward of the sheaf of constants
of the derivation. -/
def structureSheafMapToConstants
    (h : ∀ (V : Opens Y.carrier) (b : Y.presheaf.obj (op V)),
      D.d ((f.hom.c.app (op V)).hom b) = 0) :
    Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj
      (derivationConstantsSheaf hM D) :=
  ObjectProperty.homMk
    { app V := CommRingCat.ofHom
        { toFun b := ⟨(f.hom.c.app V).hom b, h V.unop b⟩
          map_one' := Subtype.ext (map_one _)
          map_mul' a b := Subtype.ext (map_mul _ a b)
          map_zero' := Subtype.ext (map_zero _)
          map_add' a b := Subtype.ext (map_add _ a b) }
      naturality V W i := by
        ext b
        exact Subtype.ext
          (congrArg (fun g => (ConcreteCategory.hom g) b) (f.hom.c.naturality i)) }

/-- `structureSheafMapToConstants` is a factorization of `f^♯`. -/
theorem structureSheafMapToConstants_comp
    (h : ∀ (V : Opens Y.carrier) (b : Y.presheaf.obj (op V)),
      D.d ((f.hom.c.app (op V)).hom b) = 0) :
    structureSheafMapToConstants f hM D h ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
          (derivationConstantsSheafι hM D) = structureSheafMap f := by
  apply Sheaf.hom_ext
  ext V b
  rfl

include hM in
/-- A relative derivation of `𝒪_X` with values in a sheaf of modules which annihilates
`d (f^♯ b)` for every local section `b` of `𝒪_Y` annihilates the whole image of the
structure map `f⁻¹ 𝒪_Y ⟶ 𝒪_X`. -/
theorem derivation_d_inverseImageStructureMap_eq_zero
    (h : ∀ (V : Opens Y.carrier) (b : Y.presheaf.obj (op V)),
      D.d ((f.hom.c.app (op V)).hom b) = 0)
    (U : (Opens X.carrier)ᵒᵖ) (a : (inverseImageSheaf f).obj.obj U) :
    D.d (((inverseImageStructureMap f).hom.app U).hom a) = 0 := by
  have key : ((sheafAdjunction f).homEquiv Y.sheaf (derivationConstantsSheaf hM D)).symm
        (structureSheafMapToConstants f hM D h) ≫ derivationConstantsSheafι hM D
      = inverseImageStructureMap f := by
    rw [inverseImageStructureMap, ← structureSheafMapToConstants_comp f hM D h,
      Adjunction.homEquiv_naturality_right_symm]
  obtain ⟨σ, hσ⟩ : ∃ σ : inverseImageSheaf f ⟶ derivationConstantsSheaf hM D,
      σ ≫ derivationConstantsSheafι hM D = inverseImageStructureMap f := ⟨_, key⟩
  have h3 := congrArg (fun (g : inverseImageSheaf f ⟶ X.sheaf) => (g.hom.app U).hom a) hσ
  exact (congrArg D.d h3.symm).trans ((σ.hom.app U).hom a).2

end Crux

section Triangle

variable {X Y S : RingedSpace.{u, u}}

/-- Two morphisms out of `Ω_{X/S}` which agree on the differentials of all local sections of
`𝒪_X` are equal: this is the uniqueness half of the universal property. -/
theorem moduleOfDifferentials_hom_ext {h : X ⟶ S}
    {T : SheafOfModules.{u} (structureSheafRing X)}
    {ψ₁ ψ₂ : moduleOfDifferentials h ⟶ T}
    (e : ∀ (U : (Opens X.carrier)ᵒᵖ) (a : X.presheaf.obj U),
      (ψ₁.val.app U).hom ((universalDerivation h).d a)
        = (ψ₂.val.app U).hom ((universalDerivation h).d a)) :
    ψ₁ = ψ₂ := by
  obtain ⟨m, -, hu⟩ := Differentials.universalDerivation_isUniversal
    (inverseImageSheaf h) X.sheaf (inverseImageStructureMap h) T
    ((universalDerivation h).postcomp ψ₁.val)
  refine (hu ψ₁ rfl).trans (hu ψ₂ ?_).symm
  apply PresheafOfModulesOfCommRing.Derivation.ext
  ext U a
  exact (e U a).symm

/-- A morphism out of `Ω_{X/S}` vanishes exactly when it annihilates the differential of
every local section of `𝒪_X`. -/
theorem moduleOfDifferentials_eq_zero_iff {h : X ⟶ S}
    {T : SheafOfModules.{u} (structureSheafRing X)}
    (ψ : moduleOfDifferentials h ⟶ T) :
    ψ = 0 ↔ ∀ (U : (Opens X.carrier)ᵒᵖ) (a : X.presheaf.obj U),
      (ψ.val.app U).hom ((universalDerivation h).d a) = 0 := by
  refine ⟨fun hψ U a => by rw [hψ]; rfl, fun e => moduleOfDifferentials_hom_ext ?_⟩
  intro U a
  rw [e U a]
  rfl

/-- The universal derivation of `X` over `Y` annihilates every section of `𝒪_X` pulled back
from `𝒪_Y`. -/
theorem universalDerivation_d_structureSheafMap (f : X ⟶ Y) (V : (Opens Y.carrier)ᵒᵖ)
    (b : Y.presheaf.obj V) :
    (universalDerivation f).d ((f.hom.c.app V).hom b) = 0 := by
  have e2 := congrArg (fun (t : Y.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf) =>
        (t.hom.app V).hom b) (unit_comp_map_inverseImageStructureMap f).symm
  exact (congrArg (universalDerivation f).d e2).trans
    (PresheafOfModulesOfCommRing.Derivation'.d_app (universalDerivation f) _)

/-- The canonical map `Ω_{X/S} ⟶ Ω_{X/Y}` attached to `f : X ⟶ Y` and `g : Y ⟶ S`: the
comparison map of Tag 08RU for the square with horizontal arrows `𝟙 X` and `g`, composed
with the identification of `(𝟙 X)^*` with the identity functor. -/
noncomputable def toRelativeDifferentials (f : X ⟶ Y) (g : Y ⟶ S) :
    moduleOfDifferentials (f ≫ g) ⟶ moduleOfDifferentials f :=
  (SheafOfModules.pullbackId (structureSheafRing X)).inv.app
      (moduleOfDifferentials (f ≫ g)) ≫
    differentialMap (𝟙 X) (f ≫ g) f g (by simp)

/-- `toRelativeDifferentials` is the adjoint transpose of the comparison map for the square
with horizontal arrows `𝟙 X` and `g`. The identification of `(𝟙 X)^*` with the identity
functor is the inverse of the unit of `(𝟙 X)^* ⊣ (𝟙 X)_*`, and `(𝟙 X)_*` is the identity. -/
theorem toRelativeDifferentials_eq (f : X ⟶ Y) (g : Y ⟶ S) :
    toRelativeDifferentials f g = RingedSpaceModuleAdjunction.homEquiv (𝟙 X)
      (moduleOfDifferentials f) (moduleOfDifferentials (f ≫ g))
      (differentialMap (𝟙 X) (f ≫ g) f g (by simp)) := by
  rw [toRelativeDifferentials, RingedSpaceModuleAdjunction.homEquiv,
    Adjunction.homEquiv_unit, SheafOfModules.pullbackId,
    Adjunction.leftAdjointIdIso_inv_app]
  simp only [SheafOfModules.pushforwardId, Iso.refl_hom, NatTrans.id_app]
  rfl

/-- The canonical map `Ω_{X/S} ⟶ Ω_{X/Y}` sends `d_{X/S} a` to `d_{X/Y} a`. -/
theorem toRelativeDifferentials_val_app_d (f : X ⟶ Y) (g : Y ⟶ S)
    (U : (Opens X.carrier)ᵒᵖ) (a : X.presheaf.obj U) :
    ((toRelativeDifferentials f g).val.app U).hom ((universalDerivation (f ≫ g)).d a)
      = (universalDerivation f).d a := by
  rw [toRelativeDifferentials_eq]
  exact differentialMap_isDifferentialMap (𝟙 X) (f ≫ g) f g (by simp) U.unop a

/-- Pushforward of sheaves of modules along a morphism of ringed spaces preserves zero
morphisms. -/
instance modulePushforward_preservesZeroMorphisms (f : X ⟶ Y) :
    (RingedSpaceModuleAdjunction.modulePushforward f).PreservesZeroMorphisms where
  map_zero A B := by
    apply (SheafOfModules.forget _).map_injective
    apply PresheafOfModules.hom_ext
    intro U
    rfl

/-- A morphism out of `Ω_{X/S}` is annihilated by the comparison map from `f^* Ω_{Y/S}`
exactly when it kills the differentials of the sections pulled back from `𝒪_Y`. -/
theorem differentialMap_comp_eq_zero_iff (f : X ⟶ Y) (g : Y ⟶ S)
    {T : SheafOfModules.{u} (structureSheafRing X)}
    (k : moduleOfDifferentials (f ≫ g) ⟶ T) :
    differentialMap f g (f ≫ g) (𝟙 S) (by simp) ≫ k = 0 ↔
      ∀ (V : (Opens Y.carrier)ᵒᵖ) (b : Y.presheaf.obj V),
        (k.val.app (op ((Opens.map f.hom.base).obj V.unop))).hom
          ((universalDerivation (f ≫ g)).d ((f.hom.c.app V).hom b)) = 0 := by
  have hzero : RingedSpaceModuleAdjunction.homEquiv f T (moduleOfDifferentials g) 0 = 0 := by
    rw [RingedSpaceModuleAdjunction.homEquiv, Adjunction.homEquiv_unit, Functor.map_zero,
      Limits.comp_zero]
  have hcomp : RingedSpaceModuleAdjunction.homEquiv f T (moduleOfDifferentials g)
        (differentialMap f g (f ≫ g) (𝟙 S) (by simp) ≫ k)
      = pushforwardDifferentialMap f g (f ≫ g) (𝟙 S) (by simp) ≫
        (RingedSpaceModuleAdjunction.modulePushforward f).map k := by
    rw [homEquiv_eq, Adjunction.homEquiv_naturality_right, ← homEquiv_eq,
      homEquiv_differentialMap]
  rw [← (RingedSpaceModuleAdjunction.homEquiv f T (moduleOfDifferentials g)).apply_eq_iff_eq,
    hzero, hcomp, moduleOfDifferentials_eq_zero_iff]
  refine forall_congr' fun V => forall_congr' fun b => ?_
  rw [comp_val_app_hom_apply, pushforwardDifferentialMap_val_app_d]
  exact Iff.rfl

/-- The canonical map to relative differentials over `Y` is an epimorphism. -/
@[stacks 0H79 "exactness at the right term", instance, ega "IV 16.4.19" "surjectivity on right"]
theorem triangleDifferentials_epi (f : X ⟶ Y) (g : Y ⟶ S) :
    Epi (toRelativeDifferentials f g) where
  left_cancellation {T} ψ₁ ψ₂ e := by
    refine moduleOfDifferentials_hom_ext fun U a => ?_
    have h1 := congrArg (fun (t : moduleOfDifferentials (f ≫ g) ⟶ T) =>
      (t.val.app U).hom ((universalDerivation (f ≫ g)).d a)) e
    have h2 : ∀ ψ : moduleOfDifferentials f ⟶ T,
        ((toRelativeDifferentials f g ≫ ψ).val.app U).hom
            ((universalDerivation (f ≫ g)).d a)
          = (ψ.val.app U).hom ((universalDerivation f).d a) := fun ψ => by
      rw [comp_val_app_hom_apply, toRelativeDifferentials_val_app_d]
    exact (h2 ψ₁).symm.trans (h1.trans (h2 ψ₂))

/-- The two comparison maps of the triangle compose to zero: the differential of a section
pulled back from `𝒪_Y` vanishes in `Ω_{X/Y}`. -/
theorem differentialMap_comp_toRelativeDifferentials (f : X ⟶ Y) (g : Y ⟶ S) :
    differentialMap f g (f ≫ g) (𝟙 S) (by simp) ≫ toRelativeDifferentials f g = 0 := by
  rw [differentialMap_comp_eq_zero_iff]
  intro V b
  rw [toRelativeDifferentials_val_app_d]
  exact universalDerivation_d_structureSheafMap f V b

section Descent

variable (f : X ⟶ Y) (g : Y ⟶ S)
  {A : SheafOfModules.{u} (structureSheafRing X)}
  (k : moduleOfDifferentials (f ≫ g) ⟶ A)
  (hk : differentialMap f g (f ≫ g) (𝟙 S) (by simp) ≫ k = 0)

/-- A morphism out of `Ω_{X/S}` annihilated by the comparison map from `f^* Ω_{Y/S}` defines
a relative derivation of `𝒪_X` over `f⁻¹ 𝒪_Y`, with the same underlying additive maps as the
derivation it defines over `(f ≫ g)⁻¹ 𝒪_S`. -/
noncomputable def derivationOfCompEqZero :
    PresheafOfModulesOfCommRing.Derivation' A.val (inverseImageStructureMap f).hom where
  d := ((universalDerivation (f ≫ g)).postcomp k.val).d
  d_mul := ((universalDerivation (f ≫ g)).postcomp k.val).d_mul
  d_map := ((universalDerivation (f ≫ g)).postcomp k.val).d_map
  d_app {U} a := derivation_d_inverseImageStructureMap_eq_zero f A.isSheaf
    ((universalDerivation (f ≫ g)).postcomp k.val)
    (fun V b => (differentialMap_comp_eq_zero_iff f g k).mp hk (op V) b) U a

/-- The factorization through `Ω_{X/Y}` of a morphism out of `Ω_{X/S}` annihilated by the
comparison map from `f^* Ω_{Y/S}`, obtained from the universal property of `Ω_{X/Y}`. -/
noncomputable def descOfCompEqZero : moduleOfDifferentials f ⟶ A :=
  Exists.choose (Differentials.universalDerivation_isUniversal
    (inverseImageSheaf f) X.sheaf (inverseImageStructureMap f) A
    (derivationOfCompEqZero f g k hk))

/-- `descOfCompEqZero` is a factorization through `toRelativeDifferentials`. -/
theorem toRelativeDifferentials_comp_descOfCompEqZero :
    toRelativeDifferentials f g ≫ descOfCompEqZero f g k hk = k := by
  refine moduleOfDifferentials_hom_ext fun U a => ?_
  rw [comp_val_app_hom_apply, toRelativeDifferentials_val_app_d]
  exact PresheafOfModulesOfCommRing.Derivation.congr_d
    (Exists.choose_spec (Differentials.universalDerivation_isUniversal
      (inverseImageSheaf f) X.sheaf (inverseImageStructureMap f) A
      (derivationOfCompEqZero f g k hk))).1 a

end Descent

/-- `Ω_{X/Y}`, with the canonical map out of `Ω_{X/S}`, is a cokernel of the comparison map
`f^* Ω_{Y/S} ⟶ Ω_{X/S}`. -/
noncomputable def isColimitCokernelCoforkToRelativeDifferentials (f : X ⟶ Y) (g : Y ⟶ S) :
    Limits.IsColimit (Limits.CokernelCofork.ofπ (toRelativeDifferentials f g)
      (differentialMap_comp_toRelativeDifferentials f g)) :=
  Limits.CokernelCofork.IsColimit.ofπ' _ _ fun k hk =>
    ⟨descOfCompEqZero f g k hk, toRelativeDifferentials_comp_descOfCompEqZero f g k hk⟩

/-- For morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ S` the canonical maps form a complex
`f^* Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y}` which is exact at `Ω_{X/S}`. Together with
`triangleDifferentials_epi` this is the exactness of `f^* Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y} ⟶ 0`. -/
@[stacks 0H79 "exactness at the middle term", ega "IV 16.4.19" "exactness at middle"]
theorem triangleDifferentials_exact (f : X ⟶ Y) (g : Y ⟶ S) :
    ∃ h : differentialMap f g (f ≫ g) (𝟙 S) (by simp) ≫ toRelativeDifferentials f g = 0,
      (ShortComplex.mk _ _ h).Exact :=
  ⟨differentialMap_comp_toRelativeDifferentials f g,
    ShortComplex.exact_of_g_is_cokernel _
      (isColimitCokernelCoforkToRelativeDifferentials f g)⟩

end Triangle

end Stacks.Sheaves.RingedSpaceDifferentials

end
