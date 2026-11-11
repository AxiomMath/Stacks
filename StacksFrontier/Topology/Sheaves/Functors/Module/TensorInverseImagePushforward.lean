module

public import StacksFrontier.Topology.Sheaves.Functors.Module.SheafAdjunctionOverPushforward
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackPresheafAdjunction
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 008Z with the explicit tensor product `𝒪 ⊗_{f^{-1}f_*𝒪} f^{-1}𝒢`

Let `f : X ⟶ Y` be a continuous map, `𝒪` a sheaf of rings on `X`, `ℱ` a sheaf of `𝒪`-modules
and `𝒢` a sheaf of `f_*𝒪`-modules. Stacks 008Z states
`Mor_{Mod(𝒪)}(𝒪 ⊗_{f^{-1}f_*𝒪} f^{-1}𝒢, ℱ) = Mor_{Mod(f_*𝒪)}(𝒢, f_*ℱ)`,
the tensor product being taken along the canonical map `f^{-1}f_*𝒪 ⟶ 𝒪`.

## Main definitions

* `TensorInverseImagePushforward.counit`: the canonical map `f^{-1}f_*𝒪 ⟶ 𝒪` of sheaves of
  commutative rings. On the model of `f^{-1}` as the sheafification of `f_p`, it is the map
  induced, by the universal property of sheafification, by the counit `f_p f_*𝒪 ⟶ 𝒪` of the
  presheaf adjunction `f_p ⊣ f_*`.
* `TensorInverseImagePushforward.tensorObj`: the sheaf of `𝒪`-modules
  `𝒪 ⊗_{f^{-1}f_*𝒪} f^{-1}𝒢`. It is `Stacks.Sheaves.RingedToposModules.extendScalars` (the
  sheafification of the sectionwise tensor product `U ↦ 𝒪(U) ⊗_{(f^{-1}f_*𝒪)(U)} (f^{-1}𝒢)(U)`,
  Stacks 0088) of the inverse image `PullbackStalkTensor.invMod` (Stacks 008X) along `counit`.
* `TensorInverseImagePushforward.tensorFunctor`: the functor `𝒢 ↦ 𝒪 ⊗_{f^{-1}f_*𝒪} f^{-1}𝒢`, whose
  value on `𝒢` is `tensorObj` on the nose.

## Main results

* `TensorInverseImagePushforward.homEquiv`: the bijection of Stacks 008Z, obtained, as in the
  source, as the composite of the bijection of Stacks 008A (in the form of the adjunction
  `Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction`) with the bijection of
  Stacks 008Y
  (itself the sheafification bijection of Stacks 0089 followed by the presheaf adjunction of
  Stacks 008U, in its explicit form `Stacks.PresheafOfModules.Pullback.pullbackModuleHomEquiv`).
* `TensorInverseImagePushforward.adjunction`: **Stacks 008Z**, `tensorFunctor ⊣ f_*`.
* `TensorInverseImagePushforward.tensorFunctorIsoTensorPullbackModule`: the explicit functor is
  isomorphic to `tensorPullbackModule`, the abstract left adjoint used in
  `StacksFrontier.Topology.Sheaves.Functors.Module.SheafAdjunctionOverPushforward`.

## Implementation notes

Rings in the Stacks project are commutative, and the explicit tensor product needs it, so `𝒪`
is a sheaf of commutative rings here. Everything lives in a single universe `u`, as in
`StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackTensor`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite Stacks.Sheafify.ModuleStalkTensor
  Stacks.PresheafOfModules.Pullback InverseImageModules PullbackStalkTensor

universe u

namespace TensorInverseImagePushforward

section Restrict

variable {C : Type*} [Category C] {R S T : Cᵒᵖ ⥤ RingCat.{u}}

/-- Restriction of scalars along an isomorphism `a : R ≅ S` of presheaves of rings is fully
faithful: for `ab = a ≫ b`, morphisms from `P` restricted along `a` to `N` restricted along `ab`
are the morphisms from `P` to `N` restricted along `b`. The underlying morphisms of presheaves of
abelian groups are unchanged. -/
noncomputable def restrictScalarsIsoHomEquiv (a : R ≅ S) (b : S ⟶ T) (ab : R ⟶ T)
    (hab : a.hom ≫ b = ab) (P : PresheafOfModules.{u} S) (N : PresheafOfModules.{u} T) :
    ((PresheafOfModules.restrictScalars a.hom).obj P ⟶
        (PresheafOfModules.restrictScalars ab).obj N) ≃
      (P ⟶ (PresheafOfModules.restrictScalars b).obj N) where
  toFun g := PresheafOfModules.homMk ((PresheafOfModules.toPresheaf R).map g) (fun X s m => by
    subst hab
    obtain ⟨r, rfl⟩ : ∃ r, (a.hom.app X).hom r = s :=
      ⟨(a.inv.app X).hom s, by rw [← RingCat.comp_apply, Iso.inv_hom_id_app]; rfl⟩
    exact (g.app X).hom.map_smul r m)
  invFun h := PresheafOfModules.homMk ((PresheafOfModules.toPresheaf S).map h) (fun X r m => by
    subst hab
    exact (h.app X).hom.map_smul ((a.hom.app X).hom r) m)
  left_inv _ := rfl
  right_inv _ := rfl

end Restrict

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (O : TopCat.Sheaf CommRingCat.{u} X)

/-- The sheaf of commutative rings `f_*𝒪` on `Y`. -/
noncomputable abbrev pushRing : TopCat.Sheaf CommRingCat.{u} Y :=
  (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj O

/-- The sheaf of rings underlying `f_*𝒪`, typed as a sheaf on the space `Y`. -/
noncomputable abbrev pushRingSheaf : TopCat.Sheaf RingCat.{u} Y :=
  ringSheaf (pushRing f O)

/-- The sheaf of rings `f^{-1}f_*𝒪` of Stacks 008X (the sheafification of `f_p f_*𝒪`), typed
as a sheaf for the topology of opens of `X`. -/
noncomputable abbrev invImageRing : Sheaf (Opens.grothendieckTopology X) RingCat.{u} :=
  inverseImageRing f (pushRingSheaf f O)

/-- The counit `f_p f_*𝒪 ⟶ 𝒪` of the presheaf adjunction `f_p ⊣ f_*`, on underlying presheaves
of rings: the transpose of the identity of `f_*𝒪`. -/
noncomputable def presheafCounit :
    pullbackRing f (ringSheaf (pushRing f O)).obj ⟶ (ringSheaf O).obj :=
  ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} f).homEquiv _ _).symm
    (𝟙 (ringSheaf (pushRing f O)).obj)

/-- The canonical map `f^{-1}f_*𝒪 ⟶ 𝒪` on underlying sheaves of rings, `f^{-1}` being the
sheafification of `f_p`: the map induced by `presheafCounit` through the universal property of
sheafification. -/
noncomputable def inverseImageCounit : invImageRing f O ⟶ ringSheaf O :=
  ((sheafificationAdjunction (Opens.grothendieckTopology X) RingCat.{u}).homEquiv _ _).symm
    (presheafCounit f O)

/-- `inverseImageCounit` restricts to `presheafCounit` along the sheafification map. -/
theorem toInverseImageRing_comp_inverseImageCounit :
    toInverseImageRing f (pushRingSheaf f O) ≫ (inverseImageCounit f O).hom =
      presheafCounit f O := by
  have h := ((sheafificationAdjunction (Opens.grothendieckTopology X) RingCat.{u}).homEquiv
    (pullbackRing f (ringSheaf (pushRing f O)).obj) (ringSheaf O)).apply_symm_apply
      (presheafCounit f O)
  rw [Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app] at h
  exact h

/-- The transpose of the canonical map under `f_p ⊣ f_*` is the identity of `f_*𝒪`. -/
theorem homEquiv_inverseImageCounit :
    (TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} f).homEquiv _ _
        (toInverseImageRing f (pushRingSheaf f O) ≫ (inverseImageCounit f O).hom) =
      𝟙 (ringSheaf (pushRing f O)).obj := by
  refine (congrArg ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} f).homEquiv _ _)
    (toInverseImageRing_comp_inverseImageCounit f O)).trans ?_
  exact Equiv.apply_symm_apply _ _

/-- On sections over `V`, the unit `f_*𝒪 ⟶ f_*f_p f_*𝒪` followed by the canonical map is the
identity of `(f_*𝒪)(V) = 𝒪(f⁻¹V)`. -/
theorem inverseImageCounit_unit_apply (V : (Opens Y)ᵒᵖ)
    (r : (ringSheaf (pushRing f O)).obj.obj V) :
    ((inverseImageCounit f O).hom.app (op ((Opens.map f).obj V.unop))).hom
        (((toInverseImageRing f (pushRingSheaf f O)).app _).hom
          (((pullbackRingUnitHom f (ringSheaf (pushRing f O)).obj).app V).hom r)) = r := by
  have h := homEquiv_inverseImageCounit f O
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg
    (fun φ : (ringSheaf (pushRing f O)).obj ⟶ (ringSheaf (pushRing f O)).obj => (φ.app V).hom r) h

/-- **The canonical map `f^{-1}f_*𝒪 ⟶ 𝒪`** of sheaves of commutative rings: `inverseImageCounit`
read on `PullbackStalkTensor.invRing`, the sheafification of `f_p` formed in `CommRingCat`,
through `PullbackStalkTensor.ringSheafInvRingIso`. -/
noncomputable def counit : invRing f (pushRing f O) ⟶ O :=
  ObjectProperty.homMk
    { app := fun U => CommRingCat.ofHom
        (((ringSheafInvRingIso f (pushRing f O)).hom ≫ inverseImageCounit f O).hom.app U).hom
      naturality := fun U V i => by
        ext x
        exact ConcreteCategory.congr_hom
          (((ringSheafInvRingIso f (pushRing f O)).hom ≫ inverseImageCounit f O).hom.naturality i)
          x }

/-- Extension of scalars along the canonical map `counit : f^{-1}f_*𝒪 ⟶ 𝒪`: the sectionwise
tensor product `𝒪(U) ⊗_{(f^{-1}f_*𝒪)(U)} -` of Stacks 03CU, sheafified (Stacks 0088). -/
noncomputable abbrev extendScalarsCounit :
    SheafOfModules.{u} (ringSheaf (invRing f (pushRing f O))) ⥤ SheafOfModules.{u} (ringSheaf O) :=
  Stacks.Sheaves.RingedToposModules.extendScalars (Opens.grothendieckTopology X) (counit f O).hom
    (ringSheaf (invRing f (pushRing f O))).property (ringSheaf O).property

/-- **The sheaf of `𝒪`-modules `𝒪 ⊗_{f^{-1}f_*𝒪} f^{-1}𝒢`** of Stacks 008Z, for a sheaf of
`f_*𝒪`-modules `𝒢`: the tensor product sheaf, i.e. the sheafification of the sectionwise tensor
product `U ↦ 𝒪(U) ⊗_{(f^{-1}f_*𝒪)(U)} (f^{-1}𝒢)(U)`, of the inverse image `f^{-1}𝒢`
(Stacks 008X) along the canonical map `counit : f^{-1}f_*𝒪 ⟶ 𝒪`. -/
noncomputable def tensorObj (G : SheafOfModules.{u} (ringSheaf (pushRing f O))) :
    SheafOfModules.{u} (ringSheaf O) :=
  (extendScalarsCounit f O).obj (invMod f (pushRing f O) G)

/-- The restriction of scalars along `counit`, right adjoint of `extendScalarsCounit`
(Stacks 03CZ). -/
noncomputable abbrev counitSheafMap :
    ringSheaf (invRing f (pushRing f O)) ⟶ ringSheaf O :=
  Stacks.Sheaves.RingedToposModules.commRingSheafMap (Opens.grothendieckTopology X)
    (counit f O).hom (ringSheaf (invRing f (pushRing f O))).property (ringSheaf O).property

variable (G : SheafOfModules.{u} (ringSheaf (pushRing f O))) (F : SheafOfModules.{u} (ringSheaf O))

/-- The inverse image `f^{-1}𝒢` of Stacks 008X, a sheaf of `f^{-1}f_*𝒪`-modules. -/
noncomputable abbrev invImageModule : SheafOfModules.{u} (invImageRing f O) :=
  inverseImageSheafOfModules f (pushRingSheaf f O) G

/-- `counit` is `inverseImageCounit` read through `PullbackStalkTensor.ringSheafInvRingIso`. -/
theorem ringSheafInvRingIso_hom_comp_inverseImageCounit :
    ((sheafToPresheaf _ _).mapIso (ringSheafInvRingIso f (pushRing f O))).hom ≫
        (inverseImageCounit f O).hom =
      (counitSheafMap f O).hom := by
  ext U : 2
  rfl

/-- Removing the transport along `PullbackStalkTensor.ringSheafInvRingIso`: morphisms
`f^{-1}𝒢 ⟶ ℱ` of sheaves of `f^{-1}f_*𝒪`-modules, read on the commutative model `invRing` or
on the model `inverseImageRing` of Stacks 008X, are the same. -/
noncomputable def invModHomEquiv :
    (invMod f (pushRing f O) G ⟶
        (SheafOfModules.restrictScalars
          (counitSheafMap f O)).obj F) ≃
      (invImageModule f O G ⟶
        (SheafOfModules.restrictScalars (inverseImageCounit f O)).obj F) :=
  ((SheafOfModules.fullyFaithfulForget.{u} (ringSheaf (invRing f (pushRing f O)))).homEquiv
      (X := invMod f (pushRing f O) G)
      (Y := (SheafOfModules.restrictScalars
          (counitSheafMap f O)).obj F)).trans
    ((restrictScalarsIsoHomEquiv
        ((sheafToPresheaf _ _).mapIso (ringSheafInvRingIso f (pushRing f O)))
        (inverseImageCounit f O).hom
        (counitSheafMap f O).hom
        (ringSheafInvRingIso_hom_comp_inverseImageCounit f O)
        (invImageModule f O G).val F.val).trans
      ((SheafOfModules.fullyFaithfulForget.{u} (invImageRing f O)).homEquiv
        (X := invImageModule f O G)
        (Y := (SheafOfModules.restrictScalars (inverseImageCounit f O)).obj F)).symm)

/-- Stacks 008Y on the explicit models: the sheafification bijection of Stacks 0089 for
`f^{-1}𝒢 = (f_p 𝒢)^#`, followed by the explicit presheaf adjunction `f_p ⊣ f_*` of
Stacks 008U. The target is `f_*ℱ` with its scalars restricted along
`f_*𝒪 ⟶ f_*f_p f_*𝒪 ⟶ f_*f^{-1}f_*𝒪 ⟶ f_*𝒪`. -/
noncomputable def inverseImageHomEquiv :
    (invImageModule f O G ⟶
        (SheafOfModules.restrictScalars (inverseImageCounit f O)).obj F) ≃
      (G.val ⟶ (PresheafOfModules.pushforward
          (pullbackRingUnitHom f (ringSheaf (pushRing f O)).obj)).obj
        ((PresheafOfModules.restrictScalars (toInverseImageRing f (pushRingSheaf f O))).obj
          ((PresheafOfModules.restrictScalars (inverseImageCounit f O).hom).obj F.val))) :=
  (PresheafOfModules.sheafifyHomEquiv (toInverseImageRing f (pushRingSheaf f O))
      (toInverseImageAb f (pushRingSheaf f O) G)
      (F := (SheafOfModules.restrictScalars (inverseImageCounit f O)).obj F)).trans
    (pullbackModuleHomEquiv f (ringSheaf (pushRing f O)).obj (M := G.val))

/-- `smul` form of `inverseImageCounit_unit_apply`, on sections of a sheaf of `𝒪`-modules. -/
theorem smul_inverseImageCounit_unit (V : (Opens Y)ᵒᵖ)
    (r : (ringSheaf O).obj.obj (op ((Opens.map f).obj V.unop)))
    (y : F.val.obj (op ((Opens.map f).obj V.unop))) :
    ((inverseImageCounit f O).hom.app (op ((Opens.map f).obj V.unop))).hom
        (((toInverseImageRing f (pushRingSheaf f O)).app _).hom
          (((pullbackRingUnitHom f (ringSheaf (pushRing f O)).obj).app V).hom r)) • y = r • y :=
  congrArg (fun s : (ringSheaf O).obj.obj (op ((Opens.map f).obj V.unop)) => s • y)
    (inverseImageCounit_unit_apply f O V r)

/-- The composite `f_*𝒪 ⟶ f_*f_p f_*𝒪 ⟶ f_*f^{-1}f_*𝒪 ⟶ f_*𝒪` is the identity
(`inverseImageCounit_unit_apply`), so restricting the scalars of `f_*ℱ` along it changes
nothing. -/
noncomputable def pushforwardHomEquiv :
    (G.val ⟶ (PresheafOfModules.pushforward
          (pullbackRingUnitHom f (ringSheaf (pushRing f O)).obj)).obj
        ((PresheafOfModules.restrictScalars (toInverseImageRing f (pushRingSheaf f O))).obj
          ((PresheafOfModules.restrictScalars (inverseImageCounit f O).hom).obj F.val))) ≃
      (G.val ⟶ ((pushforwardModule f (ringSheaf O)).obj F).val) where
  toFun g :=
    let φ := (PresheafOfModules.toPresheaf _).map g
    PresheafOfModules.homMk φ (fun V r m => by
    refine ((g.app V).hom.map_smul r m).trans ?_
    exact smul_inverseImageCounit_unit f O F V r ((g.app V).hom m))
  invFun g :=
    let φ := (PresheafOfModules.toPresheaf _).map g
    PresheafOfModules.homMk φ (fun V r m => by
    refine ((g.app V).hom.map_smul r m).trans ?_
    exact (smul_inverseImageCounit_unit f O F V r ((g.app V).hom m)).symm)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The bijection of Stacks 008Z**,
`Mor_{Mod(𝒪)}(𝒪 ⊗_{f^{-1}f_*𝒪} f^{-1}𝒢, ℱ) ≃ Mor_{Mod(f_*𝒪)}(𝒢, f_*ℱ)`. As in the source it is
the bijection of Stacks 008A, the adjunction between extension and restriction of scalars
(`Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction`, Stacks 03CZ), followed by
that of Stacks 008Y (`inverseImageHomEquiv`). -/
noncomputable def homEquiv :
    (tensorObj f O G ⟶ F) ≃ (G ⟶ (pushforwardModule f (ringSheaf O)).obj F) :=
  (Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction
        (Opens.grothendieckTopology X) (counit f O).hom
        (ringSheaf (invRing f (pushRing f O))).property (ringSheaf O).property).homEquiv
        (invMod f (pushRing f O) G) F |>.trans
    ((invModHomEquiv f O G F).trans ((inverseImageHomEquiv f O G F).trans
      ((pushforwardHomEquiv f O G F).trans
        ((SheafOfModules.fullyFaithfulForget.{u} (ringSheaf (pushRing f O))).homEquiv (X := G)
          (Y := (pushforwardModule f (ringSheaf O)).obj F)).symm)))

/-- Steps two and three of `homEquiv`, ending at morphisms out of `f_p 𝒢`. -/
noncomputable def toPullbackHom
    (h : invMod f (pushRing f O) G ⟶ (SheafOfModules.restrictScalars (counitSheafMap f O)).obj F) :
    (pullbackModuleFunctor f (ringSheaf (pushRing f O)).obj).obj G.val ⟶
      (PresheafOfModules.restrictScalars (toInverseImageRing f (pushRingSheaf f O))).obj
        ((PresheafOfModules.restrictScalars (inverseImageCounit f O).hom).obj F.val) :=
  PresheafOfModules.sheafifyHomEquiv (toInverseImageRing f (pushRingSheaf f O))
      (toInverseImageAb f (pushRingSheaf f O) G)
      (F := (SheafOfModules.restrictScalars (inverseImageCounit f O)).obj F)
    (invModHomEquiv f O G F h)

/-- `toPullbackHom` is natural in `ℱ`. -/
theorem toPullbackHom_comp {F F' : SheafOfModules.{u} (ringSheaf O)} (g : F ⟶ F')
    (h : invMod f (pushRing f O) G ⟶ (SheafOfModules.restrictScalars (counitSheafMap f O)).obj F) :
    toPullbackHom f O G F' (h ≫ (SheafOfModules.restrictScalars (counitSheafMap f O)).map g) =
      toPullbackHom f O G F h ≫
        (PresheafOfModules.restrictScalars (toInverseImageRing f (pushRingSheaf f O))).map
          ((PresheafOfModules.restrictScalars (inverseImageCounit f O).hom).map g.val) := by
  apply (PresheafOfModules.toPresheaf _).map_injective
  rfl

/-- `homEquiv` factors through `toPullbackHom` and the explicit presheaf adjunction. -/
theorem homEquiv_eq (h : tensorObj f O G ⟶ F) :
    (homEquiv f O G F h).val =
      pushforwardHomEquiv f O G F (pullbackModuleHomEquiv f _ (toPullbackHom f O G F
        ((Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction
          (Opens.grothendieckTopology X) (counit f O).hom
          (ringSheaf (invRing f (pushRing f O))).property (ringSheaf O).property).homEquiv
          (invMod f (pushRing f O) G) F h))) :=
  rfl

/-- `homEquiv` is natural in `ℱ`. -/
theorem homEquiv_naturality {F F' : SheafOfModules.{u} (ringSheaf O)} (g : F ⟶ F')
    (h : tensorObj f O G ⟶ F) :
    homEquiv f O G F' (h ≫ g) =
      homEquiv f O G F h ≫ (pushforwardModule f (ringSheaf O)).map g := by
  apply (SheafOfModules.fullyFaithfulForget _).map_injective
  apply (PresheafOfModules.toPresheaf _).map_injective
  have h1 := (Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction
    (Opens.grothendieckTopology X) (counit f O).hom
    (ringSheaf (invRing f (pushRing f O))).property
    (ringSheaf O).property).homEquiv_naturality_right h g
  set h' := (Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction
    (Opens.grothendieckTopology X) (counit f O).hom
    (ringSheaf (invRing f (pushRing f O))).property (ringSheaf O).property).homEquiv
    (invMod f (pushRing f O) G) F h
  have h2 := (pullbackModuleAdjunction f (ringSheaf (pushRing f O)).obj).homEquiv_naturality_right
    (toPullbackHom f O G F h')
    ((PresheafOfModules.restrictScalars (toInverseImageRing f (pushRingSheaf f O))).map
      ((PresheafOfModules.restrictScalars (inverseImageCounit f O).hom).map g.val))
  refine (congrArg (PresheafOfModules.toPresheaf _).map (homEquiv_eq f O G F' (h ≫ g))).trans ?_
  have e3 := (congrArg (toPullbackHom f O G F') h1).trans (toPullbackHom_comp f O G g h')
  refine (congrArg (fun z => (PresheafOfModules.toPresheaf _).map
    (pushforwardHomEquiv f O G F' (pullbackModuleHomEquiv f _ z))) e3).trans ?_
  have hPF : ∀ x, (PresheafOfModules.toPresheaf _).map (pushforwardHomEquiv f O G F' x) =
      (PresheafOfModules.toPresheaf _).map x := fun _ => rfl
  refine (hPF _).trans ?_
  refine (congrArg (PresheafOfModules.toPresheaf _).map h2).trans ?_
  rfl

/-- **The functor `𝒢 ↦ 𝒪 ⊗_{f^{-1}f_*𝒪} f^{-1}𝒢`** from sheaves of `f_*𝒪`-modules to sheaves
of `𝒪`-modules. Its value on `𝒢` is `tensorObj f O 𝒢` on the nose; its action on morphisms is
the one forced by the bijection `homEquiv`. -/
noncomputable def tensorFunctor :
    SheafOfModules.{u} (ringSheaf (pushRing f O)) ⥤ SheafOfModules.{u} (ringSheaf O) :=
  Adjunction.leftAdjointOfEquiv (G := pushforwardModule f (ringSheaf O))
    (fun G F => homEquiv f O G F) (fun G _ _ g h => homEquiv_naturality f O G g h)

/-- The value of `tensorFunctor` on `𝒢` is the explicit tensor product `tensorObj f O 𝒢`. -/
theorem tensorFunctor_obj (G : SheafOfModules.{u} (ringSheaf (pushRing f O))) :
    (tensorFunctor f O).obj G = tensorObj f O G :=
  rfl

/-- **Stacks 008Z.** Let `f : X ⟶ Y` be a continuous map, `𝒪` a sheaf of (commutative) rings on
`X`, `ℱ` a sheaf of `𝒪`-modules and `𝒢` a sheaf of `f_*𝒪`-modules. Then
`Mor_{Mod(𝒪)}(𝒪 ⊗_{f^{-1}f_*𝒪} f^{-1}𝒢, ℱ) = Mor_{Mod(f_*𝒪)}(𝒢, f_*ℱ)`, naturally: the functor
`tensorFunctor`, with `(tensorFunctor f O).obj 𝒢 = 𝒪 ⊗_{f^{-1}f_*𝒪} f^{-1}𝒢` the explicit
tensor product (the sheafified sectionwise tensor product, Stacks 0088) of the inverse image
`f^{-1}𝒢` (Stacks 008X) along the canonical map `counit : f^{-1}f_*𝒪 ⟶ 𝒪`, is left adjoint to
the pushforward `f_*`, and the hom-set bijection of the adjunction is `homEquiv`. -/
@[stacks 008Z]
noncomputable def adjunction : tensorFunctor f O ⊣ pushforwardModule f (ringSheaf O) :=
  Adjunction.adjunctionOfEquivLeft _ _

/-- The explicit functor `tensorFunctor` is isomorphic to `tensorPullbackModule`, the abstract
left adjoint of `f_*` used in
`StacksFrontier.Topology.Sheaves.Functors.Module.SheafAdjunctionOverPushforward`. -/
noncomputable def tensorFunctorIsoTensorPullbackModule :
    tensorFunctor f O ≅ tensorPullbackModule f (ringSheaf O) :=
  (adjunction f O).leftAdjointUniq (pullbackPushforwardAdjunction008Z f (ringSheaf O))

end TensorInverseImagePushforward
