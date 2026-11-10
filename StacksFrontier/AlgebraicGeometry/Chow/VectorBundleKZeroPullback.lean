module

public import StacksFrontier.AlgebraicGeometry.Chow.SecondAdamsProductRelation
public import StacksFrontier.AlgebraicGeometry.Chow.MinusAdamsOperator
public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClassTensor
public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.KernelBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.KernelHyperplaneRestriction
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Pullback on `K₀(Vect(-))`, and the second Adams operator commuting with it

Let `f : Y ⟶ X` be a morphism of schemes. Pullback of `𝒪_X`-modules induces a ring map

`f^* : K₀(Vect(X)) → K₀(Vect(Y))`, `f^*[ℰ] = [f^*ℰ]`,

and the second Adams operation commutes with it: `ψ²_Y ∘ f^* = f^* ∘ ψ²_X`.

## Main definitions

* `AlgebraicGeometry.VectorBundleKZero.pullbackAddHom`: the additive map `f^*`.
* `AlgebraicGeometry.VectorBundleKZero.pullbackRingHom`: the ring map `f^*`.

## Main results

* `AlgebraicGeometry.VectorBundleKZero.shortExact_map_pullback_of_isFiniteLocallyFree`: pullback
  along any morphism of schemes preserves a short exact sequence whose third term is finite
  locally free.
* `AlgebraicGeometry.VectorBundleKZero.secondAdamsRingHom_comp_pullbackRingHom`:
  `ψ²_Y ∘ f^* = f^* ∘ ψ²_X`.
* `AlgebraicGeometry.VectorBundleKZero.exists_secondAdamsOperator_pullbackRingHom`: a family of
  ring maps `ψ²_X` with the prescribed values on finite locally free and on invertible modules,
  compatible with pullback.

## References

* [Stacks Project, Tag 0FEJ](https://stacks.math.columbia.edu/tag/0FEJ)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.FiniteLocallyFree TopologicalSpace

universe u

namespace AlgebraicGeometry.VectorBundleKZero

variable {X Y : Scheme.{u}}

/-! ### Pullback preserves short exact sequences of finite locally free modules -/

/-- An epimorphism onto a finite locally free module splits at every stalk. -/
theorem isSplitEpi_stalkFunctor_map_of_isFiniteLocallyFree {E G : X.Modules} (q : E ⟶ G)
    (hq : Epi q) (hG : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G) (x : X) :
    IsSplitEpi ((AlgebraicGeometry.SheafOfModules.stalkFunctor
      (structureSheafRing X.toRingedSpace) x).map q) := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G :=
    isFiniteLocallyFree_toSheaf hG
  have hfree : @Module.Free (ToType (X.toRingedSpace.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk G.val.presheaf x)) _ _
      (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace G.val x) := by
    have h := (Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree G x).1
    rw [Stacks.SheafOfModules.stalkModule_eq X.toRingedSpace G.val x]
    exact h
  let := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace E.val x
  let := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace G.val x
  have : Module.Projective
      (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace x)
      (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X.toRingedSpace G.val x) :=
    @Module.Projective.of_free _ _ _ _ _ hfree
  have hepi : Epi ((AlgebraicGeometry.SheafOfModules.stalkFunctor
      (structureSheafRing X.toRingedSpace) x).map q) := by
    have : Epi (C := SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) q := hq
    exact (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (structureSheafRing X.toRingedSpace) x).map_epi q
  have hsurj : Function.Surjective
      (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X.toRingedSpace E.val G.val
        q.val x) :=
    (ModuleCat.epi_iff_surjective _).mp hepi
  obtain ⟨s, hs⟩ := Module.projective_lifting_property
    (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X.toRingedSpace E.val G.val q.val x)
      LinearMap.id hsurj
  refine IsSplitEpi.mk' ⟨ModuleCat.ofHom
    { toFun := s
      map_add' := fun a b => s.map_add a b
      map_smul' := fun r m => ?_ }, ?_⟩
  · exact (congrArg s (Stacks.RingedSpace.smul_stalkObj_eq X.toRingedSpace x G r m)).trans
      ((s.map_smul (Stacks.RingedSpace.toCommRingStalk X.toRingedSpace x r) m).trans
        (Stacks.RingedSpace.smul_stalkObj_eq X.toRingedSpace x E r (s m)).symm)
  · ext m
    exact LinearMap.congr_fun hs m

/-- Pullback along any morphism of schemes preserves a short exact sequence whose third term is
finite locally free. -/
theorem shortExact_map_pullback_of_isFiniteLocallyFree (f : Y ⟶ X) {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (hG : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) S.X₃) :
    (S.map (Scheme.Modules.pullback f)).ShortExact := by
  have := hS.epi_g
  have hk : Mono ((Scheme.Modules.pullback f).map (kernel.ι S.g)) :=
    Stacks.RingedSpace.mono_modulePullback_map_kernel_ι_of_isSplitEpi_stalk
      f.toLRSHom.toShHom S.g fun y =>
        isSplitEpi_stalkFunctor_map_of_isFiniteLocallyFree S.g hS.epi_g hG _
  have he : kernel.lift S.g S.f S.zero ≫ kernel.ι S.g = S.f := kernel.lift_ι _ _ _
  have : Mono (kernel.lift S.g S.f S.zero) := by
    have := hS.mono_f
    exact mono_of_mono_fac he
  have : Epi (kernel.lift S.g S.f S.zero) := (ShortComplex.exact_iff_epi_kernel_lift S).1 hS.exact
  have : IsIso (kernel.lift S.g S.f S.zero) := isIso_of_mono_of_epi _
  have hm : Mono ((Scheme.Modules.pullback f).map S.f) := by
    rw [← he, Functor.map_comp]
    infer_instance
  exact shortExact_map_pullback_of_mono f hS hm

/-! ### The ring map `f^*` -/

/-- `ℰ ↦ [f^*ℰ]` on finite locally free modules, and zero elsewhere. -/
def classOfPullback (f : Y ⟶ X) (M : X.Modules) : VectorBundleKZero Y :=
  open scoped Classical in
  if IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M then
    classOf Y ((Scheme.Modules.pullback f).obj M) else 0

/-- For a finite locally free module `M`, `classOfPullback f M` is the class `[f^*M]`. -/
theorem classOfPullback_of_isFiniteLocallyFree (f : Y ⟶ X) (M : X.Modules)
    (hM : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M) :
    classOfPullback f M = classOf Y ((Scheme.Modules.pullback f).obj M) := by
  simp only [classOfPullback, hM, ite_true]

/-- The additive map `f^* : K₀(Vect(X)) → K₀(Vect(Y))`. -/
def pullbackAddHom (f : Y ⟶ X) : VectorBundleKZero X →+ VectorBundleKZero Y :=
  liftAddHom (classOfPullback f)
    (fun M hM => by simp only [classOfPullback, hM, ite_false])
    (fun {E F G} a b w hE hF hG hmono hepi hex => by
      rw [classOfPullback_of_isFiniteLocallyFree f F hF,
        classOfPullback_of_isFiniteLocallyFree f E hE,
        classOfPullback_of_isFiniteLocallyFree f G hG]
      have hS : (ShortComplex.mk a b w).ShortExact := ShortComplex.ShortExact.mk' hex hmono hepi
      have hS' := shortExact_map_pullback_of_isFiniteLocallyFree f hS hG
      exact @classOf_shortExact Y _ _ _ _ _ hS'.mono_f hS'.epi_g _
        (isFiniteLocallyFree_pullback f E hE) (isFiniteLocallyFree_pullback f F hF)
        (isFiniteLocallyFree_pullback f G hG) hS'.exact)

/-- The additive map `f^*` satisfies `f^*[M] = [f^*M]` for a finite locally free module `M`. -/
theorem pullbackAddHom_classOf (f : Y ⟶ X) (M : X.Modules)
    (hM : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M) :
    pullbackAddHom f (classOf X M) = classOf Y ((Scheme.Modules.pullback f).obj M) :=
  (liftAddHom_classOf _ _ _ M).trans (classOfPullback_of_isFiniteLocallyFree f M hM)

/-- `f^*([M] * [N]) = f^*[M] * f^*[N]` for finite locally free modules `M` and `N`. -/
theorem pullbackAddHom_classOf_mul (f : Y ⟶ X) (M N : X.Modules)
    (hM : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M)
    (hN : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) N) :
    pullbackAddHom f (classOf X M * classOf X N) =
      pullbackAddHom f (classOf X M) * pullbackAddHom f (classOf X N) := by
  have hMN : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (Scheme.Modules.tensorObjRingedSpace X M N) := @isFiniteLocallyFree_tensorObj X M N hM hN
  rw [classOf_mul M N hM hN, pullbackAddHom_classOf f _ hMN, pullbackAddHom_classOf f M hM,
    pullbackAddHom_classOf f N hN,
    classOf_mul _ _ (isFiniteLocallyFree_pullback f M hM) (isFiniteLocallyFree_pullback f N hN)]
  exact classOf_eq_of_iso (Stacks.Chow.pullbackTensorObjIso f M N)
    (isFiniteLocallyFree_pullback f _ hMN)

/-- The pullback ring map `f^* : K₀(Vect(X)) → K₀(Vect(Y))`, `f^*[ℰ] = [f^*ℰ]`. -/
def pullbackRingHom (f : Y ⟶ X) : VectorBundleKZero X →+* VectorBundleKZero Y where
  toFun := pullbackAddHom f
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    refine (pullbackAddHom_classOf f _ (isFiniteLocallyFree_unit X)).trans ?_
    exact classOf_eq_of_iso (Scheme.Modules.pullbackUnitIso f)
      (isFiniteLocallyFree_pullback f _ (isFiniteLocallyFree_unit X))
  map_mul' a b := by
    have h1 : ∀ M : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M →
        ∀ b, pullbackAddHom f (classOf X M * b) =
          pullbackAddHom f (classOf X M) * pullbackAddHom f b := by
      intro M hM
      have h : (pullbackAddHom f).comp (AddMonoidHom.mulLeft (classOf X M)) =
          (AddMonoidHom.mulLeft (pullbackAddHom f (classOf X M))).comp (pullbackAddHom f) :=
        addHom_ext fun N hN => pullbackAddHom_classOf_mul f M N hM hN
      exact fun b => DFunLike.congr_fun h b
    have h : (pullbackAddHom f).comp (AddMonoidHom.mulRight b) =
        (AddMonoidHom.mulRight (pullbackAddHom f b)).comp (pullbackAddHom f) :=
      addHom_ext fun M hM => h1 M hM b
    exact DFunLike.congr_fun h a

/-- `f^*[ℰ] = [f^*ℰ]` on finite locally free modules. -/
theorem pullbackRingHom_classOf (f : Y ⟶ X) (M : X.Modules)
    (hM : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M) :
    pullbackRingHom f (classOf X M) = classOf Y ((Scheme.Modules.pullback f).obj M) :=
  pullbackAddHom_classOf f M hM

/-! ### The second Adams operator commutes with `f^*` -/

/-- The second Adams operation commutes with pullback: `ψ²_Y ∘ f^* = f^* ∘ ψ²_X`, for the
operations `secondAdamsRingHom (squarePowersData -)` of `X` and `Y`. -/
theorem secondAdamsRingHom_comp_pullbackRingHom (f : Y ⟶ X) :
    (secondAdamsRingHom (squarePowersData Y)).comp (pullbackRingHom f) =
      (pullbackRingHom f).comp (secondAdamsRingHom (squarePowersData X)) :=
  RingHom.ext fun a => secondAdamsAddHom_pullback f (squarePowersData Y) (squarePowersData X)
    (pullbackRingHom f) (pullbackRingHom_classOf f) (isFiniteLocallyFree_pullback f) a

/-- For every scheme `X` there is a ring map `ψ²_X : K₀(Vect(X)) → K₀(Vect(X))` with
`ψ²_X([ℰ]) = [Sym² ℰ] - [⋀² ℰ]` on finite locally free modules, `ψ²_X([ℒ]) = [ℒ ⊗ ℒ]` on
invertible modules, and compatible with pullbacks: for every morphism `f : Y ⟶ X`,
`ψ²_Y ∘ f^* = f^* ∘ ψ²_X`, where `f^*` is the pullback ring map `pullbackRingHom f`. -/
@[stacks 0FEJ "the family of ring maps `ψ²_X`, its value on finite locally free and on \
  invertible modules, and its compatibility with pullback `ψ²_Y ∘ f^* = f^* ∘ ψ²_X` for the \
  pullback ring map `f^*` of `K₀(Vect(-))` constructed here; no hypothesis"]
theorem exists_secondAdamsOperator_pullbackRingHom :
    ∃ ψ : ∀ X : Scheme.{u}, VectorBundleKZero X →+* VectorBundleKZero X,
      (∀ (X : Scheme.{u}) (E : X.Modules),
          IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
            ψ X (classOf X E) =
              classOf X (secondSymmetricPower X E) - classOf X (secondExteriorPower X E)) ∧
        (∀ (X : Scheme.{u}) (L : X.Modules),
          Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L →
            ψ X (classOf X L) = classOf X (Scheme.Modules.tensorObjRingedSpace X L L)) ∧
        (∀ {X Y : Scheme.{u}} (f : Y ⟶ X),
          (ψ Y).comp (pullbackRingHom f) = (pullbackRingHom f).comp (ψ X)) :=
  ⟨fun X => secondAdamsRingHom (squarePowersData X),
    fun X E hE => secondAdamsAddHom_classOf (squarePowersData X) E hE,
    fun X L hL => have := hL; secondAdamsAddHom_classOf_isInvertible (squarePowersData X) L,
    fun f => secondAdamsRingHom_comp_pullbackRingHom f⟩

end AlgebraicGeometry.VectorBundleKZero

end
