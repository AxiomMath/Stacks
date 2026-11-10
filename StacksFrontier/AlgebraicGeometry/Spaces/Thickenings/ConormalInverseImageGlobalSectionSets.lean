module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageRestrictScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InverseImageUnitSection
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionIdealCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalInverseImageSections

/-!
# Global sections of sheaves of sets along the inclusion of a thickening

Let `i : Z ⟶ X` be the inclusion of a closed subspace of an algebraic space. The direct image of
modules along `i` has two presentations — restriction of scalars along `i♯ : i⁻¹𝒪_X ⟶ 𝒪_Z` followed
by the transport along `i_*` (`AlgebraicGeometry.Space.thickeningTransport`), and
`AlgebraicGeometry.Space.modulePushforward` — and this file records how the structure maps between
them act on underlying sheaves of sets, on global sections `⊤ ⟶ F` of sheaves of sets: the
structure map `𝒪_X ⟶ i_*𝒪_Z` carries the unit section to the unit section, the identification
`𝒪_X ≅ i_*i⁻¹𝒪_X` of a thickening is the unit of `i⁻¹ ⊣ i_*` on sheaves of sets, and the
comparison of the two direct images is the identity on sheaves of sets. For a first-order
thickening, this computes the inclusion `𝒞_{Z/X} ⟶ i⁻¹𝒪_X` on the classes of ideal sections, on
sheaves of sets.

## Main results

* `Stacks.SheafOfModules.IdealTransport.eqToHom_restrictScalars_comp_transport_app`: along an
  equality of ring maps, the comparison of the restrictions of scalars commutes with the
  transport.
* `AlgebraicGeometry.Space.ringOneHom_comp_map_homEquiv_modulePullbackUnitIso_hom`: the structure
  map `𝒪_X ⟶ i_*𝒪_Z` carries the unit section to the unit section.
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_thickeningUnitTransportIso_hom`: for a
  thickening, `𝒪_X ≅ i_*i⁻¹𝒪_X` is the unit of `i⁻¹ ⊣ i_*` on sheaves of sets.
* `AlgebraicGeometry.Space.moduleSheafFunctor_structureRingSheaf_map_modulePushforwardIso_inv_app`:
  the comparison of the two direct images is the identity on sheaves of sets.
* `AlgebraicGeometry.Space.ringOneHom_comp_map_thickeningTransportIso_inv_app`: the comparison of
  the two direct images fixes the unit section of `i_*𝒪_Z`.
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_thickeningTransport_map_comp`: the transport
  presentation of the direct image is `i_*` on underlying sheaves of sets.
* `AlgebraicGeometry.Space.ringOneHom_comp_map_conormalInverseImageι_modulePullbackGlobalSection`:
  for a first-order thickening, the inclusion `𝒞_{Z/X} ⟶ i⁻¹𝒪_X` on the class `i^*s` of a global
  section `s` of the ideal is `i⁻¹` of the global section `⊤ ⟶ 𝓘 ⊆ 𝒪_X`, on sheaves of sets
  (transposed along `i⁻¹ ⊣ i_*`).

## References

* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

universe u

namespace Stacks.SheafOfModules.IdealTransport

open Stacks.Sheaves.ToposPullback

variable {C : Type*} [Category C] (J : GrothendieckTopology C) {D : Type*} [Category D]
  {K : GrothendieckTopology D}
  [J.HasSheafCompose (CategoryTheory.forget RingCat.{u})]
  [K.HasSheafCompose (CategoryTheory.forget RingCat.{u})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u})]
  (Φ : Sheaf K (Type u) ⥤ Sheaf J (Type u)) [PreservesFiniteProducts Φ]
  {R : Sheaf J RingCat.{u}} {Λ Q : Sheaf K RingCat.{u}} (η : R ⟶ pullbackRingSheaf J Φ Λ)

omit [J.HasSheafCompose (CategoryTheory.forget RingCat.{u})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u})] in
/-- Along an equality of ring maps `φ = ψ : Λ ⟶ Q`, the comparison of the two restrictions of
scalars followed by the transport is the transport of the comparison. -/
theorem eqToHom_restrictScalars_comp_transport_app {φ ψ : Λ ⟶ Q} (h : φ = ψ)
    (N : _root_.SheafOfModules.{u} Q) :
    (eqToHom (congrArg (fun χ ↦ _root_.SheafOfModules.restrictScalars χ ⋙ transport J Φ η)
      h)).app N = (transport J Φ η).map
        ((eqToHom (congrArg (fun χ ↦ _root_.SheafOfModules.restrictScalars χ) h)).app N) := by
  subst h
  simp

omit [K.HasSheafCompose (CategoryTheory.forget RingCat.{u})] in
/-- Along an equality of ring maps `φ = ψ : Λ ⟶ Q`, the comparison of the two restrictions of
scalars is the identity on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_eqToHom_restrictScalars_app {φ ψ : Λ ⟶ Q} (h : φ = ψ)
    (N : _root_.SheafOfModules.{u} Q) :
    (Sheaf.moduleSheafFunctor Λ).map
      ((eqToHom (congrArg (fun χ ↦ _root_.SheafOfModules.restrictScalars χ) h)).app N) =
        𝟙 ((Sheaf.moduleSheafFunctor Λ).obj ((_root_.SheafOfModules.restrictScalars φ).obj N)) := by
  subst h
  simp

/-- The inverse of `eqToIso p ≪≫ e`, seen after a functor `M`, on a morphism `x` into its source:
when `x` followed by `e⁻¹` is `x'`, the result is any morphism heterogeneously equal to `x'`. -/
theorem _root_.CategoryTheory.comp_map_inv_app_eqToIso_trans_of_heq {𝒜 ℬ 𝒞 : Type*}
    [Category 𝒜] [Category ℬ] [Category 𝒞] {F G H : 𝒜 ⥤ ℬ} (p : F = G) (e : G ≅ H)
    (M : ℬ ⥤ 𝒞) {N : 𝒜} {T : 𝒞} {x : T ⟶ M.obj (H.obj N)} {x' : T ⟶ M.obj (G.obj N)}
    {y : T ⟶ M.obj (F.obj N)} (he : x ≫ M.map (e.inv.app N) = x') (hy : HEq x' y) :
    x ≫ M.map ((eqToIso p ≪≫ e).inv.app N) = y := by
  subst p
  rw [Iso.trans_inv, NatTrans.comp_app, CategoryTheory.Functor.map_comp, ← Category.assoc, he,
    eqToIso_refl, Iso.refl_inv, NatTrans.id_app, CategoryTheory.Functor.map_id, Category.comp_id]
  exact eq_of_heq hy

/-- For a functor `G`, `c ≫ G(o ≫ w) = x ≫ η` as soon as `c ≫ G o = o'` and
`o' ≫ G w = x ≫ η`. -/
theorem _root_.CategoryTheory.comp_map_comp_eq_of_comp_map_eq {𝒞 𝒟 : Type*} [Category 𝒞]
    [Category 𝒟] (G : 𝒟 ⥤ 𝒞) {T X : 𝒞} {A B T' : 𝒟} (c : T ⟶ G.obj T') (o : T' ⟶ A)
    (w : A ⟶ B) (o' : T ⟶ G.obj A) (x : T ⟶ X) (η : X ⟶ G.obj B) (hc : c ≫ G.map o = o')
    (hk : o' ≫ G.map w = x ≫ η) : c ≫ G.map (o ≫ w) = x ≫ η := by
  rw [G.map_comp, ← Category.assoc, hc, hk]

/-- For a functor `M`, from `H ≫ τ ≫ a ≫ b = s ≫ j ≫ u` and the values of `M` on the pieces,
`o ≫ g = (r ≫ M(s ≫ j)) ≫ η`. -/
theorem _root_.CategoryTheory.comp_eq_comp_map_comp_of_comp_eq {𝒜 𝒞 : Type*} [Category 𝒜]
    [Category 𝒞] (M : 𝒜 ⥤ 𝒞) {T₀ : 𝒞} {U₀ P Q Q' Q'' I : 𝒜} {H : U₀ ⟶ P} {τ : P ⟶ Q}
    {a : Q ⟶ Q'} {b : Q' ⟶ Q''} {s : U₀ ⟶ I} {j : I ⟶ U₀} {u : U₀ ⟶ Q''}
    (key : H ≫ τ ≫ a ≫ b = s ≫ j ≫ u) (r : T₀ ⟶ M.obj U₀) (o : T₀ ⟶ M.obj Q)
    {g : M.obj Q ⟶ M.obj Q''} {η : M.obj U₀ ⟶ M.obj Q''} (hHτ : (r ≫ M.map H) ≫ M.map τ = o)
    (hab : M.map a ≫ M.map b = g) (hu : M.map u = η) :
    o ≫ g = (r ≫ M.map (s ≫ j)) ≫ η := by
  subst hHτ hab hu
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, key]

/-- `CategoryTheory.comp_eq_comp_map_comp_of_comp_eq` for `τ = (eqToIso p ≪≫ e).inv.app N`, with
the hypothesis on `(r ≫ M H) ≫ M τ` replaced by `r ≫ M H = o₁`, `o₁ ≫ M(e.inv.app N) = o₁'` and
`HEq o₁' o`. -/
theorem _root_.CategoryTheory.comp_eq_comp_map_comp_of_comp_eqToIso_trans_eq {𝒜 𝒞 𝒵 : Type*}
    [Category 𝒜] [Category 𝒞] [Category 𝒵] (M : 𝒜 ⥤ 𝒞) {F G K : 𝒵 ⥤ 𝒜} (p : F = G)
    (e : G ≅ K) {N : 𝒵} {T₀ : 𝒞} {U₀ Q' Q'' I : 𝒜} {H : U₀ ⟶ K.obj N}
    {a : F.obj N ⟶ Q'} {b : Q' ⟶ Q''} {s : U₀ ⟶ I} {j : I ⟶ U₀} {u : U₀ ⟶ Q''}
    (key : H ≫ (eqToIso p ≪≫ e).inv.app N ≫ a ≫ b = s ≫ j ≫ u) (r : T₀ ⟶ M.obj U₀)
    {o₁ : T₀ ⟶ M.obj (K.obj N)} {o₁' : T₀ ⟶ M.obj (G.obj N)} (o : T₀ ⟶ M.obj (F.obj N))
    {g : M.obj (F.obj N) ⟶ M.obj Q''} {η : M.obj U₀ ⟶ M.obj Q''}
    (hA : r ≫ M.map H = o₁) (he : o₁ ≫ M.map (e.inv.app N) = o₁') (hH : HEq o₁' o)
    (hab : M.map a ≫ M.map b = g) (hu : M.map u = η) :
    o ≫ g = (r ≫ M.map (s ≫ j)) ≫ η :=
  CategoryTheory.comp_eq_comp_map_comp_of_comp_eq M key r o
    ((congrArg (· ≫ _) hA).trans (CategoryTheory.comp_map_inv_app_eqToIso_trans_of_heq p e M he hH))
    hab hu

end Stacks.SheafOfModules.IdealTransport

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-- **The structure map `𝒪_X ⟶ i_*𝒪_Z` carries the unit section to the unit section.** -/
theorem ringOneHom_comp_map_homEquiv_modulePullbackUnitIso_hom :
    ringOneHom (structureRingSheaf B S hS X) ≫
        (moduleSheafFunctor (structureRingSheaf B S hS X)).map
          ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).homEquiv _ _
              (modulePullbackUnitIso B S hS (subspaceInclusion B S hS X Z)).hom) =
      ringOneHom (Stacks.Sheaves.ToposPullback.pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
        (SmallEtale.topology B S hS X.1)
        (thickeningToposHom B S hS Z).pushforward
        (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))) := by
  refine hom_ext_sections fun W _ ↦ ?_
  exact (congrArg (fun m ↦ m.val.app W (1 : (structureRingSheaf B S hS X).obj.obj W))
      (homEquiv_modulePullbackUnitIso_hom B S hS (subspaceInclusion B S hS X Z))).trans
    ((structureSharp B S hS (subspaceInclusion B S hS X Z)).hom.app W).hom.map_one

/-- `𝒪_X ≅ i_*i⁻¹𝒪_X` is, on underlying sheaves of sets, the unit of `i⁻¹ ⊣ i_*`. -/
theorem moduleSheafFunctor_map_thickeningUnitTransportIso_hom (hZ : IsThickening B S hS X Z.1) :
    (moduleSheafFunctor (structureRingSheaf B S hS X)).map
        (thickeningUnitTransportIso B S hS Z hZ).hom =
      (thickeningToposHom B S hS Z).adj.unit.app
        ((moduleSheafFunctor (structureRingSheaf B S hS X)).obj
          (SheafOfModules.unit (structureRingSheaf B S hS X))) :=
  hom_ext_sections fun _ _ ↦ rfl

/-- The comparison of the two direct images of modules is the identity on underlying sheaves of
sets, read backwards. -/
theorem moduleSheafFunctor_structureRingSheaf_map_modulePushforwardIso_inv_app
    {Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (N : Modules.{u, u} B S hS Y.1 Y.2) :
    (moduleSheafFunctor (structureRingSheaf B S hS X)).map
        ((modulePushforwardIso B S hS f).inv.app N) =
      𝟙 ((smallEtaleDirectImage B S hS f).obj (moduleSetSheaf B S hS Y N)) :=
  (Category.comp_id _).symm.trans ((congrArg ((moduleSheafFunctor
    (structureRingSheaf B S hS X)).map ((modulePushforwardIso B S hS f).inv.app N) ≫ ·)
      (moduleSheafFunctor_map_modulePushforwardIso_hom_app B S hS f N).symm).trans
    (((moduleSheafFunctor (structureRingSheaf B S hS X)).map_comp _ _).symm.trans
      ((congrArg (moduleSheafFunctor (structureRingSheaf B S hS X)).map
        ((modulePushforwardIso B S hS f).inv_hom_id_app N)).trans
          ((moduleSheafFunctor (structureRingSheaf B S hS X)).map_id _))))

/-- The unit section of `i_*𝒪_Z` is fixed by the comparison of the two direct images. -/
private theorem ringOneHom_comp_map_modulePushforwardIso_inv_app_unit :
    ringOneHom (Stacks.Sheaves.ToposPullback.pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
      (SmallEtale.topology B S hS X.1) (thickeningToposHom B S hS Z).pushforward
      (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))) ≫
      (moduleSheafFunctor (structureRingSheaf B S hS X)).map
        ((modulePushforwardIso B S hS (subspaceInclusion B S hS X Z)).inv.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).2).O))) =
    ringOneHom (Stacks.Sheaves.ToposPullback.pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
      (SmallEtale.topology B S hS X.1) (thickeningToposHom B S hS Z).pushforward
      (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))) := by
  rw [moduleSheafFunctor_structureRingSheaf_map_modulePushforwardIso_inv_app]
  exact Category.comp_id _

/-- The unit section of `i_*𝒪_Z`, as a section of the direct image `i_*` of the unit module. -/
private theorem heq_ringOneHom_pushforwardModules_unit :
    @HEq (⊤_ _ ⟶ (moduleSheafFunctor (structureRingSheaf B S hS X)).obj
      ((Stacks.Sheaves.RingedToposModules.pushforwardModules
        (smallEtaleRingedToposModulesHom B S hS (subspaceInclusion B S hS X Z))).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).2).O))))
      (ringOneHom (Stacks.Sheaves.ToposPullback.pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
      (SmallEtale.topology B S hS X.1) (thickeningToposHom B S hS Z).pushforward
      (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))))
      _ (ringOneHom (Stacks.Sheaves.ToposPullback.pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
      (SmallEtale.topology B S hS X.1) (thickeningToposHom B S hS Z).pushforward
      (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)))) :=
  HEq.rfl

/-- The unit section of `i_*𝒪_Z`, as a section of the transported unit module. -/
private theorem heq_ringOneHom_restrictScalars_unit :
    @HEq
      _ (ringOneHom (Stacks.Sheaves.ToposPullback.pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
      (SmallEtale.topology B S hS X.1) (thickeningToposHom B S hS Z).pushforward
      (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))))
      (⊤_ _ ⟶ (moduleSheafFunctor (structureRingSheaf B S hS X)).obj
        ((SheafOfModules.restrictScalars (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS X Z)) ⋙ thickeningTransport B S hS Z).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).2).O))))
      (ringOneHom (Stacks.Sheaves.ToposPullback.pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
      (SmallEtale.topology B S hS X.1) (thickeningToposHom B S hS Z).pushforward
      (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)))) :=
  HEq.rfl

/-- **The comparison of the two presentations of the direct image of modules along the
inclusion of a closed subspace fixes the unit section** of `i_*𝒪_Z`, on sheaves of sets. -/
theorem ringOneHom_comp_map_thickeningTransportIso_inv_app :
    ringOneHom (Stacks.Sheaves.ToposPullback.pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
      (SmallEtale.topology B S hS X.1) (thickeningToposHom B S hS Z).pushforward
      (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))) ≫
      (moduleSheafFunctor (structureRingSheaf B S hS X)).map
        ((thickeningTransportIso B S hS Z).inv.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1
              (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).2).O))) =
    ringOneHom (Stacks.Sheaves.ToposPullback.pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
      (SmallEtale.topology B S hS X.1) (thickeningToposHom B S hS Z).pushforward
      (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))) := by
  have r := CategoryTheory.comp_map_inv_app_eqToIso_trans_of_heq
    (restrictScalars_comp_thickeningTransport B S hS Z)
    (modulePushforwardIso B S hS (subspaceInclusion B S hS X Z))
    (moduleSheafFunctor (structureRingSheaf B S hS X))
    (ringOneHom_comp_map_modulePushforwardIso_inv_app_unit B S hS Z)
    ((heq_ringOneHom_pushforwardModules_unit B S hS Z).trans
      (heq_ringOneHom_restrictScalars_unit B S hS Z))
  have ht : thickeningTransportIso B S hS Z =
      eqToIso (restrictScalars_comp_thickeningTransport B S hS Z) ≪≫
        modulePushforwardIso B S hS (subspaceInclusion B S hS X Z) := rfl
  rw [ht]
  exact r

/-- The direct image of modules along the inclusion of a closed subspace, in the presentation
`AlgebraicGeometry.Space.thickeningTransport`, is the direct image `i_*` of sheaves of sets on
underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_thickeningTransport_map_comp
    {M₁ M₂ M₃ : SheafOfModules.{u}
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))}
    (a : M₁ ⟶ M₂) (b : M₂ ⟶ M₃) :
    (moduleSheafFunctor (structureRingSheaf B S hS X)).map
        ((thickeningTransport B S hS Z).map a) ≫
      (moduleSheafFunctor (structureRingSheaf B S hS X)).map
        ((thickeningTransport B S hS Z).map b) =
    (thickeningToposHom B S hS Z).pushforward.map
      ((moduleSheafFunctor (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS X Z))).map (a ≫ b)) := by
  have h {M M' : SheafOfModules.{u}
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))} (c : M ⟶ M') :
      (moduleSheafFunctor (structureRingSheaf B S hS X)).map
        ((thickeningTransport B S hS Z).map c) =
      (thickeningToposHom B S hS Z).pushforward.map
        ((moduleSheafFunctor (structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS X Z))).map c) :=
    hom_ext_sections fun _ _ ↦ rfl
  rw [h a, h b]
  exact ((thickeningToposHom B S hS Z).pushforward.map_comp _ _).symm.trans
    (congrArg (thickeningToposHom B S hS Z).pushforward.map
      ((moduleSheafFunctor (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS X Z))).map_comp a b).symm)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for discrete limits of presheaves on the small étale site exceeds the
-- default budget
/-- Discrete limits of presheaves of sets on the small étale site (instance search times out
without this shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_ConormalInverseImageGlobalSectionSets
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (J : Type u) :
    HasLimitsOfShape (Discrete J) ((SmallEtale B S hS F)ᵒᵖ ⥤ Type u) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for discrete limits of presheaves on the small étale site exceeds the
-- default budget
/-- Discrete limits indexed by `Type` of presheaves of sets on the small étale site (instance
search times out without this shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete₀_ConormalInverseImageGlobalSectionSets
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (J : Type) :
    HasLimitsOfShape (Discrete J) ((SmallEtale B S hS F)ᵒᵖ ⥤ Type u) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for discrete limits of sheaves on the small étale site exceeds the
-- default budget
/-- Discrete limits of sheaves of sets on the small étale site (instance search times out
without this shortcut). -/
local instance (priority := high) hasDiscreteLimits_topos_ConormalInverseImageGlobalSectionSets
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (J : Type) :
    HasLimitsOfShape (Discrete J) (Sheaf (SmallEtale.topology B S hS F) (Type u)) :=
  letI : HasLimitsOfShape (Discrete J) (Type u) := inferInstance
  letI : HasLimitsOfShape (Discrete J) ((SmallEtale B S hS F)ᵒᵖ ⥤ Type u) :=
    hasLimitsOfShape_discrete₀_ConormalInverseImageGlobalSectionSets B S hS F J
  letI : CreatesLimitsOfShape (Discrete J)
      (sheafToPresheaf (SmallEtale.topology B S hS F) (Type u)) :=
    Sheaf.createsLimitsOfShape
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (sheafToPresheaf (SmallEtale.topology B S hS F) (Type u))

/-- The terminal sheaf of sets on the small étale site (instance search times out without this
shortcut). -/
local instance (priority := high) hasTerminal_topos_ConormalInverseImageGlobalSectionSets
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    HasTerminal (Sheaf (SmallEtale.topology B S hS F) (Type u)) :=
  hasDiscreteLimits_topos_ConormalInverseImageGlobalSectionSets B S hS F PEmpty

/-- **The inclusion of the conormal module on the class of an ideal section, on sheaves of
sets**: for a first-order thickening `i : Z ⟶ X` and a global section `s` of its defining ideal
`𝓘`, the unit section followed by `i^*s` and `𝒞_{Z/X} ⟶ i⁻¹𝒪_X` is the image along `i⁻¹` of the
global section `⊤ ⟶ 𝓘 ⊆ 𝒪_X`. -/
theorem ringOneHom_comp_map_conormalInverseImageι_modulePullbackGlobalSection
    (hZ : IsFirstOrderThickening B S hS X Z.1)
    (s : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶
      (definingIdealSheaf B S hS X Z).toSheafOfModules) :
    ringOneHom (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) ≫
        (moduleSheafFunctor (structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS X Z))).map
          ((SheafOfModules.restrictScalars (structureSharpRingInverseImage B S hS
              (subspaceInclusion B S hS X Z))).map
              (modulePullbackGlobalSection B S hS (subspaceInclusion B S hS X Z) s) ≫
            conormalInverseImageι B S hS Z hZ) =
      (thickeningToposHom B S hS Z).inverseImage.globalSectionMap
        (ringOneHom (structureRingSheaf B S hS X) ≫
          (moduleSheafFunctor (structureRingSheaf B S hS X)).map
            (s ≫ (definingIdealSheaf B S hS X Z).ι)) := by
  have key := thickeningTransport_map_conormalInverseImageι_modulePullbackGlobalSection B S hS
    Z hZ s
  have ht : thickeningTransportIso B S hS Z =
      eqToIso (restrictScalars_comp_thickeningTransport B S hS Z) ≪≫
        modulePushforwardIso B S hS (subspaceInclusion B S hS X Z) := rfl
  rw [ht] at key
  have : HasTerminal (smallEtaleRingedTopos B S hS X).Topos :=
    hasTerminal_topos_ConormalInverseImageGlobalSectionSets B S hS X.1
  have : HasTerminal
      (smallEtaleRingedTopos B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).Topos :=
    hasTerminal_topos_ConormalInverseImageGlobalSectionSets B S hS _
  have : PreservesLimit (Functor.empty.{0} _) (thickeningToposHom B S hS Z).inverseImage :=
    have := (thickeningToposHom B S hS Z).preservesFiniteLimits
    inferInstance
  have : PreservesLimit (Functor.empty.{0} _) (thickeningToposHom B S hS Z).pushforward :=
    have := (thickeningToposHom B S hS Z).adj.rightAdjoint_preservesLimits
    inferInstance
  refine Adjunction.eq_globalSectionMap_of_comp_map_eq (thickeningToposHom B S hS Z).adj _ _
    (CategoryTheory.inv (terminalComparison (thickeningToposHom B S hS Z).pushforward)) ?_
  refine CategoryTheory.comp_map_comp_eq_of_comp_map_eq _ _ _ _ _ _ _
    ((congrArg (_ ≫ ·) (Stacks.Sheaves.ToposPushforward.ringOneHom_comp
      (SmallEtale.topology B S hS X.1) (thickeningToposHom B S hS Z).pushforward _)).trans
      (IsIso.inv_hom_id_assoc _ _)) ?_
  exact CategoryTheory.comp_eq_comp_map_comp_of_comp_eqToIso_trans_eq
    (moduleSheafFunctor (structureRingSheaf B S hS X))
    (restrictScalars_comp_thickeningTransport B S hS Z)
    (modulePushforwardIso B S hS (subspaceInclusion B S hS X Z)) key
    (ringOneHom (structureRingSheaf B S hS X))
    (ringOneHom
      (Stacks.Sheaves.ToposPullback.pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
        (SmallEtale.topology B S hS X.1) (thickeningToposHom B S hS Z).pushforward
        (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))))
    (ringOneHom_comp_map_homEquiv_modulePullbackUnitIso_hom B S hS Z)
    (ringOneHom_comp_map_modulePushforwardIso_inv_app_unit B S hS Z)
    ((heq_ringOneHom_pushforwardModules_unit B S hS Z).trans
      (heq_ringOneHom_restrictScalars_unit B S hS Z))
    (moduleSheafFunctor_map_thickeningTransport_map_comp B S hS Z _ _)
    (moduleSheafFunctor_map_thickeningUnitTransportIso_hom B S hS Z hZ.1)

end AlgebraicGeometry.Space

end
