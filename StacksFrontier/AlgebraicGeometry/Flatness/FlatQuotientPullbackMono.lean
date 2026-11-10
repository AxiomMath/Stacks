module

public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.Localization
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctors.FlatPullbackStalk
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat

/-!
# A short exact sequence with flat third term stays exact after any base change

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes and let `0 → K → G → Q → 0` be a short exact sequence of
`𝒪_X`-modules with `Q` flat over `S`. Then `(g')^*K → (g')^*G` is still a monomorphism, that is,
the pulled-back sequence `0 → (g')^*K → (g')^*G → (g')^*Q → 0` is again short exact. This is the
vanishing of `Tor_1` against a module flat over the base, read at the level of sheaves.

## Main results

* `LinearMap.injective_baseChange_of_flat_cokernel`: the algebraic statement. If
  `0 → M → N → P → 0` is an exact sequence of `A`-modules with `P` flat over a ring `R` below
  `A`, and `C` is a flat `A ⊗_R B`-algebra for an `R`-algebra `B`, then `C ⊗_A M → C ⊗_A N` is
  injective.
* `AlgebraicGeometry.injective_stalkMapLinear_modulePullback_of_injective_baseChange`: the stalk
  of the pullback of a homomorphism of sheaves of modules is injective as soon as the base change
  of the stalk of the homomorphism along the germ map is.
* `AlgebraicGeometry.Scheme.Modules.mono_pullback_map_of_shortExact_of_isFlatOver`: **the
  sheaf statement.**

## Implementation notes

The proof is stalkwise and needs no quasi-coherence. At a point `x'` of `X'` with images
`x ∈ X`, `t' ∈ S'` and `t ∈ S`, the stalk of the pullback of `K → G` is
`𝒪_{X',x'} ⊗_{𝒪_{X,x}} (K_x → G_x)` (Stacks 0098), and `𝒪_{X',x'}` is a localization of
`𝒪_{X,x} ⊗_{𝒪_{S,t}} 𝒪_{S',t'}`
(`AlgebraicGeometry.BaseChangeStalk.pullback_stalk_isLocalization`). Writing `T` for that tensor
product, `𝒪_{X',x'} ⊗_{𝒪_{X,x}} K_x = 𝒪_{X',x'} ⊗_T (T ⊗_{𝒪_{X,x}} K_x)` and
`T ⊗_{𝒪_{X,x}} K_x = 𝒪_{S',t'} ⊗_{𝒪_{S,t}} K_x`. The map `𝒪_{S',t'} ⊗ K_x → 𝒪_{S',t'} ⊗ G_x`
is injective because `Q_x` is flat over `𝒪_{S,t}` (Mathlib's
`LinearMap.lTensor_injective_of_exact_of_flat`), and a localization is flat.

The cartesian square is arbitrary; the statement is first proved for Mathlib's chosen pullback
and then transported along the comparison isomorphism, which is flat.

## References

* [Stacks Project, Tag 00HL](https://stacks.math.columbia.edu/tag/00HL)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct Opposite TopologicalSpace

universe u

/-! ### The algebraic statement -/

section Algebra

variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra A C] [Algebra (A ⊗[R] B) C]
  [IsScalarTower A (A ⊗[R] B) C]
  {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module A M] [Module A N] [Module A P] [Module R M] [Module R N] [Module R P]
  [IsScalarTower R A M] [IsScalarTower R A N] [IsScalarTower R A P]

/-- Base change along `A → A ⊗_R B` of an `A`-linear map `g` is, up to the canonical
identification `(A ⊗_R B) ⊗_A M ≅ B ⊗_R M`, the base change of `g` along `R → B`. -/
theorem LinearMap.injective_baseChange_tensorProduct_of_injective_lTensor (g : M →ₗ[A] N)
    (hg : Function.Injective ((g.restrictScalars R).lTensor B)) :
    Function.Injective (g.baseChange (A ⊗[R] B)) := by
  let eM : (A ⊗[R] B) ⊗[A] M ≃+ B ⊗[R] M :=
    ((TensorProduct.comm A (A ⊗[R] B) M).toAddEquiv.trans
      (AlgebraTensorModule.cancelBaseChange R A A M B).toAddEquiv).trans
      (TensorProduct.comm R M B).toAddEquiv
  let eN : (A ⊗[R] B) ⊗[A] N ≃+ B ⊗[R] N :=
    ((TensorProduct.comm A (A ⊗[R] B) N).toAddEquiv.trans
      (AlgebraTensorModule.cancelBaseChange R A A N B).toAddEquiv).trans
      (TensorProduct.comm R N B).toAddEquiv
  have hcomm : ∀ z, eN (g.baseChange (A ⊗[R] B) z) = (g.restrictScalars R).lTensor B (eM z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul t m =>
      induction t using TensorProduct.inductionOn with
      | add t s ht hs => simp only [TensorProduct.add_tmul, map_add, ht, hs]
      | tmul a b =>
        simp [eM, eN, AlgebraTensorModule.cancelBaseChange_tmul]
  intro z w hzw
  apply eM.injective
  apply hg
  rw [← hcomm, ← hcomm, hzw]

/-- **Tor-vanishing against a module flat over the base, after a flat extension.** Let
`0 → M → N → P → 0` be exact over `A` with `P` flat over a ring `R` below `A`, let `B` be an
`R`-algebra and `C` a flat `A ⊗_R B`-algebra. Then `C ⊗_A M → C ⊗_A N` is injective. -/
theorem LinearMap.injective_baseChange_of_flat_cokernel [Module.Flat (A ⊗[R] B) C]
    [Module.Flat R P] (g : M →ₗ[A] N) (f : N →ₗ[A] P) (hg : Function.Injective g)
    (hf : Function.Surjective f) (hgf : Function.Exact g f) :
    Function.Injective (g.baseChange C) := by
  have h1 : Function.Injective (g.baseChange (A ⊗[R] B)) :=
    g.injective_baseChange_tensorProduct_of_injective_lTensor
      (LinearMap.lTensor_injective_of_exact_of_flat (f.restrictScalars R) hf
        (g.restrictScalars R) hg hgf B)
  have h2 : Function.Injective ((g.baseChange (A ⊗[R] B)).baseChange C) := by
    rw [LinearMap.baseChange_eq_lTensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ h1
  let cM := AlgebraTensorModule.cancelBaseChange A (A ⊗[R] B) C C M
  let cN := AlgebraTensorModule.cancelBaseChange A (A ⊗[R] B) C C N
  rw [LinearMap.baseChange_baseChange] at h2
  have h3 : Function.Injective (cN.symm ∘ g.baseChange C ∘ cM) := h2
  exact (Function.Injective.of_comp_iff' _ cM.bijective).1 ((cN.symm.injective.of_comp_iff _).1 h3)

end Algebra

/-! ### The stalk of a pullback map as a base change -/

namespace AlgebraicGeometry

open Stacks.ModuleSkyscraper RingedSpaceModuleAdjunction

/-- The stalk at `x` of the pullback `f^*φ` of a homomorphism of sheaves of modules is
injective as soon as the base change along `𝒪_{Y,f(x)} → 𝒪_{X,x}` of the stalk of `φ` at
`f(x)` is: the two are identified by the canonical isomorphism
`(f^*G)_x ≅ 𝒪_{X,x} ⊗_{𝒪_{Y,f(x)}} G_{f(x)}` of Stacks 0098. -/
theorem injective_stalkMapLinear_modulePullback_of_injective_baseChange
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G H : _root_.SheafOfModules.{u} (structureSheafRing Y)) (φ : G ⟶ H) (x : X) :
    letI : Algebra (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x) :=
      (f.hom.stalkMap x).hom.toAlgebra
    Function.Injective ((stalkMapLinear (R := Y.presheaf)
        (M := G.val) (N := H.val) φ.val (f.hom.base x)).baseChange (X.presheaf.stalk x)) →
    Function.Injective (stalkMapLinear (R := X.presheaf)
        (M := ((modulePullback f).obj G).val) (N := ((modulePullback f).obj H).val)
        ((modulePullback f).map φ).val x) := by
  classical
  let R := Y.presheaf.stalk (f.hom.base x)
  let S := X.presheaf.stalk x
  let _ : Algebra R S := (f.hom.stalkMap x).hom.toAlgebra
  intro hq
  let M := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) G.val.presheaf (f.hom.base x)
  let M' := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) H.val.presheaf (f.hom.base x)
  let N := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
    ((modulePullback f).obj G).val.presheaf x
  obtain ⟨E, hE⟩ := exists_modulePullbackStalkLinearEquiv f G x
  obtain ⟨E', hE'⟩ := exists_modulePullbackStalkLinearEquiv f H x
  set a := stalkMapLinear (R := Y.presheaf) (M := G.val) (N := H.val) φ.val (f.hom.base x)
  set b := stalkMapLinear (R := X.presheaf)
    (M := ((modulePullback f).obj G).val) (N := ((modulePullback f).obj H).val)
    ((modulePullback f).map φ).val x
  let qS : TensorProduct R S M →ₗ[S] TensorProduct R S M' := LinearMap.baseChange S a
  let lhs : TensorProduct R S M →ₗ[S] TensorProduct R S M' :=
    E'.toLinearMap.comp (b.comp E.symm.toLinearMap)
  have hgen : ∀ m : M, lhs (1 ⊗ₜ[R] m) = qS (1 ⊗ₜ[R] m) := by
    intro m
    obtain ⟨V, hxV, s, hs⟩ :=
      TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) G.val.presheaf m
    let uG := ((modulePullbackPushforwardAdjunction f).unit.app G).val.app (op V) s
    let z := TopCat.Presheaf.germ ((modulePullback f).obj G).val.presheaf
      ((opensMap f).obj V) x hxV uG
    have hunitG : E z = (1 : S) ⊗ₜ[R] m := by
      rw [← hs]
      exact hE V hxV s
    have hsec : (((modulePullback f).map φ).val.app (op ((opensMap f).obj V))).hom uG =
        ((modulePullbackPushforwardAdjunction f).unit.app H).val.app (op V)
          ((φ.val.app (op V)).hom s) :=
      congrArg (fun r : G ⟶ (modulePushforward f).obj ((modulePullback f).obj H) ↦
        (r.val.app (op V)).hom s) ((modulePullbackPushforwardAdjunction f).unit_naturality φ)
    have hφgerm : a m = TopCat.Presheaf.germ H.val.presheaf V (f.hom.base x) hxV
        ((φ.val.app (op V)).hom s) := by
      rw [← hs]
      exact stalkMapLinear_germ (R := Y.presheaf) (M := G.val) (N := H.val) φ.val
        (f.hom.base x) V hxV s
    change E' (b (E.symm (1 ⊗ₜ[R] m))) = qS (1 ⊗ₜ[R] m)
    rw [E.symm_apply_eq.2 hunitG.symm, stalkMapLinear_germ (R := X.presheaf)
      (M := ((modulePullback f).obj G).val) (N := ((modulePullback f).obj H).val)
      ((modulePullback f).map φ).val x ((opensMap f).obj V) hxV uG, hsec,
      hE' V hxV ((φ.val.app (op V)).hom s), ← hφgerm]
    rfl
  have hmaps : ∀ z : TensorProduct R S M, lhs z = qS z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => simp [hz, hw]
    | tmul s m => rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul, map_smul, hgen]
  have hcomm : ∀ n : N, E' (b n) = qS (E n) := fun n ↦
    (congrArg (fun y ↦ E' (b y)) (E.symm_apply_apply n).symm).trans (hmaps (E n))
  exact fun n m hnm ↦
    E.injective (hq ((hcomm n).symm.trans ((congrArg E' hnm).trans (hcomm m))))

/-! ### The sheaf statement -/

/-- The stalks of a short exact sequence of `𝒪_X`-modules form an injective map followed by a
surjective one, exact in the middle. -/
private theorem stalk_shortExact {X : Scheme.{u}} {T : ShortComplex X.Modules}
    (hT : T.ShortExact) (x : X) :
    Function.Injective (stalkMapLinear (R := X.presheaf) (M := T.X₁.val) (N := T.X₂.val)
        T.f.val x) ∧
      Function.Surjective (stalkMapLinear (R := X.presheaf) (M := T.X₂.val) (N := T.X₃.val)
        T.g.val x) ∧
      Function.Exact (stalkMapLinear (R := X.presheaf) (M := T.X₁.val) (N := T.X₂.val)
        T.f.val x) (stalkMapLinear (R := X.presheaf) (M := T.X₂.val) (N := T.X₃.val)
        T.g.val x) := by
  refine ⟨(SheafOfModules.mono_iff_injective_stalkMap T.f).1 hT.mono_f x,
    (SheafOfModules.epi_iff_surjective_stalkMap T.g).1 hT.epi_g x, ?_⟩
  have hex := (SheafOfModules.exact_iff_stalkFunctor_map_exact
    (O := X.ringCatSheaf) (T : ShortComplex (_root_.SheafOfModules.{u} X.ringCatSheaf))).1
      hT.exact x
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hex

/-- The statement for Mathlib's chosen pullback `X ×_S S'`. -/
private theorem mono_pullback_fst_map_of_shortExact_of_isFlatOver {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) {T : ShortComplex X.Modules} (hT : T.ShortExact)
    (hQ : IsFlatOver f.toLRSHom.toShHom T.X₃) :
    Mono ((Scheme.Modules.pullback (Limits.pullback.fst f g)).map T.f) := by
  refine (SheafOfModules.mono_iff_injective_stalkMap _).2 fun t ↦ ?_
  let pX : Limits.pullback f g ⟶ X := Limits.pullback.fst f g
  let pY : Limits.pullback f g ⟶ S' := Limits.pullback.snd f g
  refine injective_stalkMapLinear_modulePullback_of_injective_baseChange pX.toLRSHom.toShHom
    T.X₁ T.X₂ T.f t ?_
  let x := pX.base t
  let y := pY.base t
  have hxy : (pX ≫ f).base t = (pY ≫ g).base t :=
    congrArg (fun k : Limits.pullback f g ⟶ S => k.base t) Limits.pullback.condition
  let R := S.presheaf.stalk ((pX ≫ f).base t)
  let A := X.presheaf.stalk x
  let B := S'.presheaf.stalk y
  let C := (Limits.pullback f g).presheaf.stalk t
  let _ : Algebra R A := (f.stalkMap x).hom.toAlgebra
  let _ : Algebra R B :=
    (eqToHom (congrArg S.presheaf.stalk hxy) ≫ g.stalkMap y).hom.toAlgebra
  obtain ⟨φ, hleft, -, W, hlocal⟩ :=
    AlgebraicGeometry.BaseChangeStalk.pullback_stalk_isLocalization f g t
  let _ : Algebra (A ⊗[R] B) C := φ.toAlgebra
  have _ : IsLocalization W C := hlocal
  have _ : Module.Flat (A ⊗[R] B) C := IsLocalization.flat C W
  let _ : Algebra A C := (pX.stalkMap t).hom.toAlgebra
  have _ : IsScalarTower A (A ⊗[R] B) C := IsScalarTower.of_algebraMap_eq' hleft.symm
  let P₁ : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := T.X₁.val
  let P₂ : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := T.X₂.val
  let P₃ : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := T.X₃.val
  let M₁ := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) P₁.presheaf x
  let M₂ := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) P₂.presheaf x
  let M₃ := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) P₃.presheaf x
  let _ : Module A M₁ := inferInstance
  let _ : Module A M₂ := inferInstance
  let _ : Module A M₃ := inferInstance
  let _ : Module R M₁ := Module.compHom M₁ (f.stalkMap x).hom
  let _ : Module R M₂ := Module.compHom M₂ (f.stalkMap x).hom
  let _ : Module R M₃ := Module.compHom M₃ (f.stalkMap x).hom
  have _ : IsScalarTower R A M₁ := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have _ : IsScalarTower R A M₂ := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have _ : IsScalarTower R A M₃ := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have _ : Module.Flat R M₃ := hQ x
  obtain ⟨hi, hs, he⟩ := stalk_shortExact hT x
  exact LinearMap.injective_baseChange_of_flat_cokernel (R := R) (A := A) (B := B)
    (C := C) (M := M₁) (N := M₂) (P := M₃) _ _ hi hs he

/-- **A short exact sequence whose third term is flat over the base stays short exact after any
base change.** Let `X' = X ×_S S'` be presented by a cartesian square with projections
`g' : X' ⟶ X` and `f' : X' ⟶ S'`, and let `0 → K → G → Q → 0` be a short exact sequence of
`𝒪_X`-modules with `Q` flat over `S`. Then `(g')^*K ⟶ (g')^*G` is a monomorphism. This is the
vanishing of `Tor_1^{𝒪_S}(Q, 𝒪_{S'})`; no quasi-coherence is needed. -/
theorem Scheme.Modules.mono_pullback_map_of_shortExact_of_isFlatOver
    {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (h : IsPullback g' f' f g) {T : ShortComplex X.Modules} (hT : T.ShortExact)
    (hQ : IsFlatOver f.toLRSHom.toShHom T.X₃) :
    Mono ((Scheme.Modules.pullback g').map T.f) := by
  have key : Mono ((Scheme.Modules.pullback
      (h.isoPullback.hom ≫ Limits.pullback.fst f g)).map T.f) := by
    have _ := mono_pullback_fst_map_of_shortExact_of_isFlatOver f g hT hQ
    have _ : Mono ((Scheme.Modules.pullback h.isoPullback.hom).map
        ((Scheme.Modules.pullback (Limits.pullback.fst f g)).map T.f)) :=
      Scheme.Modules.mono_pullback_map_of_flat h.isoPullback.hom _ inferInstance
    rw [← NatIso.naturality_1 (Scheme.Modules.pullbackComp h.isoPullback.hom
      (Limits.pullback.fst f g)) T.f]
    dsimp only [Functor.comp_map]
    infer_instance
  rwa [h.isoPullback_hom_fst] at key

end AlgebraicGeometry
