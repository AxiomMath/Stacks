module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Kernel
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.PullbackIdealPower
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.RestrictOpen

/-!
# The comparison map from the completion of a direct image

Let `f : X ⟶ Y` be a morphism of locally Noetherian schemes, let `𝒥 ⊆ 𝒪_Y` be a quasi-coherent
sheaf of ideals, write `ℐ = 𝒥.comap f` for the inverse-image ideal sheaf on `X`, and let `𝓕` be
a coherent `𝒪_X`-module whose direct image `f_*𝓕` is coherent as well. There is a canonical map

`c_n : (f_*𝓕) / 𝒥 ⁿ⁺¹ (f_*𝓕) ⟶ f_*(𝓕 / ℐ ⁿ⁺¹𝓕)`

for every `n`, and these maps are compatible with the transition maps of the two inverse
systems, so they assemble into a morphism of inverse systems from the completion of `f_*𝓕`
along `𝒥` to the direct image of the completion of `𝓕` along `ℐ`.

The content is that the direct image of the projection `𝓕 ⟶ 𝓕 / ℐ ⁿ⁺¹𝓕` annihilates the
subsheaf `𝒥 ⁿ⁺¹ (f_*𝓕)`: a section `a` of `𝒥 ⁿ⁺¹` over an affine open `U` of `Y` pulls back to
a section of `ℐ ⁿ⁺¹` over `f^{-1}U`, so `a • x` already lies in `ℐ ⁿ⁺¹𝓕` for every section `x`
of `𝓕` over `f^{-1}U`. The map `c_n` is then the factorization of the direct image of the
projection through the quotient.

## Main definitions

* `Stacks.Coherent.pushforwardCompletionComponent` — the map `c_n`.
* `Stacks.Coherent.pushforwardCompletionComparison` — **the morphism of inverse systems `c`**,
  whose component at `n` is `c_n`.

## Main results

* `Stacks.Coherent.pushforward_idealPowerMultiple_comp_eq_zero` — the direct image of a map
  killing `ℐ ⁿ M` kills `𝒥 ⁿ (f_*M)`.
* `Stacks.Coherent.pushforwardCompletionComponent_π` — **the computation rule**: the projection
  of `f_*𝓕` onto the `n`-th term of its completion, followed by `c_n`, is the direct image of
  the projection of `𝓕` onto the `n`-th term of its completion.
* `Stacks.Coherent.pushforwardCompletionComparison_app` — the component of `c` at `n` is `c_n`.

## Implementation notes

The annihilation statement goes through
`Stacks.Algebraization.submodule_ι_comp_eq_zero_iff`, which turns the vanishing of a composite
with the inclusion of a subsheaf into containment in the sectionwise kernel, and
`Stacks.Algebraization.idealPowerMultiple_le_iff`, the affine-local universal property of the
subsheaf `𝒥 ⁿ M`. Pulling a section of `𝒥 ⁿ` back is
`Stacks.Algebraization.appLE_mem_comap_pow`; since `f^{-1}U` need not be affine, the resulting
membership is first checked on a cover of `f^{-1}U` by affine opens and then transferred by
locality of the subsheaf.

The completion functor is zero-indexed, so its `n`-th term is the quotient by the `(n+1)`-st
power of the ideal; `Stacks.Algebraization.completionFunctor_obj` identifies that term with
`Stacks.Algebraization.idealPowerQuotient`, and the `eqToHom` of that identification is what
`pushforwardCompletionComponent` composes with the cokernel factorization.

Naturality of `c` is checked after cancelling the projection of `f_*𝓕`, which is an epimorphism
by `Stacks.Coherent.epi_completionProjection`; both triangles then reduce to the computation
rule and to `Stacks.Algebraization.completionProjection_naturality`.

Instance search does not see through the semireducible definition
`AlgebraicGeometry.Scheme.Modules` to the zero morphisms of `X.Modules` when the source is
presented as a bare `SheafOfModules X.ringCatSheaf`, which is how the sheaf of modules
underlying a subsheaf is presented; the local instance below supplies them, as in
`StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.PullbackIdealPower`.

## References

* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

/-- The zero morphism out of the sheaf of modules underlying a subsheaf. Instance search does not
see through `AlgebraicGeometry.Scheme.Modules`, a semireducible definition, to find the zero
morphisms of `X.Modules` for a source presented as a bare `SheafOfModules X.ringCatSheaf`. -/
local instance zeroHomOfSheafOfModules {X : Scheme.{u}}
    (A : SheafOfModules.{u} X.ringCatSheaf) (B : X.Modules) : Zero (A ⟶ B) :=
  Limits.HasZeroMorphisms.zero (C := X.Modules) A B

/-! ### Annihilation of the ideal-power multiple of a direct image -/

/-- **Pulling a section of `𝒥 ⁿ` back into `ℐ ⁿ M`.** If `a` is a section of the `n`-th power of
`𝒥` over an affine open `U` of the target and `x` is a section of `M` over an open `V` of the
source contained in `f^{-1}U`, then `f^♯(a) • x` is a section of the subsheaf
`(𝒥.comap f) ⁿ M` over `V`.

The subsheaf is described by its sections over affine opens, so the statement is checked on a
cover of `V` by affine opens contained in `V` and then transferred by locality. -/
private lemma appLE_smul_mem_idealPowerMultiple {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : Y.IdealSheafData) (n : ℕ) (M : X.Modules) (U : Y.affineOpens) (a : Γ(Y, U))
    (ha : a ∈ J.ideal U ^ n) (V : X.Opens) (hVU : V ≤ f ⁻¹ᵁ (U : Y.Opens)) (x : Γ(M, V)) :
    (f.appLE (U : Y.Opens) V hVU).hom a • x ∈
      (Stacks.Algebraization.idealPowerMultiple (J.comap f) n M).toSubmodule.obj (op V) := by
  let P := Stacks.Algebraization.idealPowerMultiple (J.comap f) n M
  refine P.isSheaf ((f.appLE (U : Y.Opens) V hVU).hom a • x) ?_
  rw [Opens.mem_grothendieckTopology]
  intro z hz
  obtain ⟨V', ⟨W, hWaff, rfl⟩, hzV', hV'V⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hz V.2
  let T : X.affineOpens := ⟨W, hWaff⟩
  have hTV : (T : X.Opens) ≤ V := hV'V
  refine ⟨T, homOfLE hTV, ?_, hzV'⟩
  have hmem := (Stacks.Algebraization.idealPowerMultiple_le_iff (J.comap f) n M P).mp le_rfl T
    (Submodule.smul_mem_smul
      (Stacks.Algebraization.appLE_mem_comap_pow f J n U T (hTV.trans hVU) ha)
      (Submodule.mem_top (x := M.presheaf.map (homOfLE hTV).op x)))
  have hres : (f.appLE (U : Y.Opens) (T : X.Opens) (hTV.trans hVU)).hom a •
        M.presheaf.map (homOfLE hTV).op x =
      M.presheaf.map (homOfLE hTV).op ((f.appLE (U : Y.Opens) V hVU).hom a • x) := by
    rw [Scheme.Modules.map_smul M (homOfLE hTV)]
    congr 1
    exact (congrArg (fun k : Γ(Y, (U : Y.Opens)) ⟶ Γ(X, (T : X.Opens)) => k.hom a)
      (f.appLE_map hVU (homOfLE hTV).op)).symm
  rwa [hres] at hmem

/-- `𝒥 ^ n (f_* M) ⟶ N` vanishes when `ℐ ^ n M ⟶ M ⟶ N'` does. -/
public lemma pushforward_idealPowerMultiple_comp_eq_zero
    {X Y : Scheme.{u}} (f : X ⟶ Y) (J : Y.IdealSheafData) (n : ℕ)
    {M N : X.Modules} (g : M ⟶ N)
    (hg : (Stacks.Algebraization.idealPowerMultiple (J.comap f) n M).ι ≫ g = 0) :
    (Stacks.Algebraization.idealPowerMultiple J n
        ((Scheme.Modules.pushforward f).obj M)).ι ≫
      (Scheme.Modules.pushforward f).map g = 0 := by
  replace hg := (Stacks.Algebraization.submodule_ι_comp_eq_zero_iff _ g).mp hg
  refine (Stacks.Algebraization.submodule_ι_comp_eq_zero_iff _ _).mpr ?_
  refine (Stacks.Algebraization.idealPowerMultiple_le_iff J n _ _).mpr fun U => ?_
  refine Submodule.smul_le.mpr fun a ha x _ => ?_
  have happ : f.appLE (U : Y.Opens) (f ⁻¹ᵁ (U : Y.Opens)) le_rfl = f.app (U : Y.Opens) := by
    simp [Scheme.Hom.appLE]
  have hmem := appLE_smul_mem_idealPowerMultiple f J n M U a ha
    (f ⁻¹ᵁ (U : Y.Opens)) le_rfl x
  rw [happ] at hmem
  exact hg (op (f ⁻¹ᵁ (U : Y.Opens))) hmem

/-! ### The comparison map -/

/-- The projection onto the `n`-th term of the completion kills the subsheaf `I ⁿ⁺¹ F`, being
the projection onto the quotient by that subsheaf followed by an identification of the target. -/
public lemma completionProjection_idealPowerMultiple_comp {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ) :
    (Stacks.Algebraization.idealPowerMultiple I (n + 1) F.obj).ι ≫
      Stacks.Algebraization.completionProjection X I F n = 0 :=
  (Category.assoc (obj := X.Modules)
        ((Stacks.Algebraization.idealPowerMultiple I (n + 1) F.obj).ι :
          ((Stacks.Algebraization.idealPowerMultiple I (n + 1) F.obj).toSheafOfModules :
            X.Modules) ⟶ F.obj)
        (cokernel.π (C := X.Modules)
          ((Stacks.Algebraization.idealPowerMultiple I (n + 1) F.obj).ι :
            ((Stacks.Algebraization.idealPowerMultiple I (n + 1) F.obj).toSheafOfModules :
              X.Modules) ⟶ F.obj))
        (eqToHom (Stacks.Algebraization.completionFunctor_obj X I F n).symm)).symm.trans
    ((congrArg (· ≫ eqToHom (Stacks.Algebraization.completionFunctor_obj X I F n).symm)
        (cokernel.condition (C := X.Modules)
          ((Stacks.Algebraization.idealPowerMultiple I (n + 1) F.obj).ι :
            ((Stacks.Algebraization.idealPowerMultiple I (n + 1) F.obj).toSheafOfModules :
              X.Modules) ⟶ F.obj))).trans
      Limits.zero_comp)

/-- **The comparison map at level `n`**, from the `n`-th term of the completion of `f_*𝓕` along
`𝒥` to the direct image of the `n`-th term of the completion of `𝓕` along `𝒥.comap f`.

It is the factorization of the direct image of the projection `𝓕 ⟶ 𝓕 / ℐ ⁿ⁺¹𝓕` through the
quotient by `𝒥 ⁿ⁺¹ (f_*𝓕)`, which is legitimate by
`Stacks.Coherent.pushforward_idealPowerMultiple_comp_eq_zero`. -/
public def pushforwardCompletionComponent {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (J : Y.IdealSheafData) (F : X.Modules) [F.IsCoherent]
    [((Scheme.Modules.pushforward f).obj F).IsCoherent] (n : ℕ) :
    ((Stacks.Algebraization.completionFunctor Y J).obj
      ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩).obj.obj (op n) ⟶
      (Scheme.Modules.pushforward f).obj
        (((Stacks.Algebraization.completionFunctor X (J.comap f)).obj
          ⟨F, inferInstance⟩).obj.obj (op n)) :=
  eqToHom (Stacks.Algebraization.completionFunctor_obj Y J
      ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩ n) ≫
    cokernel.desc (C := Y.Modules) (Stacks.Algebraization.idealPowerMultiple J (n + 1)
      ((Scheme.Modules.pushforward f).obj F)).ι
      ((Scheme.Modules.pushforward f).map
        (Stacks.Algebraization.completionProjection X (J.comap f) ⟨F, inferInstance⟩ n))
      (pushforward_idealPowerMultiple_comp_eq_zero f J (n + 1) _
        (completionProjection_idealPowerMultiple_comp (J.comap f) ⟨F, inferInstance⟩ n))

/-- **The computation rule for the comparison map.** The projection of `f_*𝓕` onto the `n`-th
term of its completion, followed by the comparison map, is the direct image of the projection of
`𝓕` onto the `n`-th term of its completion. -/
public lemma pushforwardCompletionComponent_π {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (J : Y.IdealSheafData) (F : X.Modules) [F.IsCoherent]
    [((Scheme.Modules.pushforward f).obj F).IsCoherent] (n : ℕ) :
    Stacks.Algebraization.completionProjection Y J
        ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩ n ≫
      pushforwardCompletionComponent f J F n =
        (Scheme.Modules.pushforward f).map
          (Stacks.Algebraization.completionProjection X (J.comap f) ⟨F, inferInstance⟩ n) := by
  change (cokernel.π (C := Y.Modules) (Stacks.Algebraization.idealPowerMultiple J (n + 1)
          ((Scheme.Modules.pushforward f).obj F)).ι ≫
        eqToHom (Stacks.Algebraization.completionFunctor_obj Y J
          ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩ n).symm) ≫
      (eqToHom (Stacks.Algebraization.completionFunctor_obj Y J
            ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩ n) ≫
          cokernel.desc (C := Y.Modules) (Stacks.Algebraization.idealPowerMultiple J (n + 1)
            ((Scheme.Modules.pushforward f).obj F)).ι
            ((Scheme.Modules.pushforward f).map
              (Stacks.Algebraization.completionProjection X (J.comap f) ⟨F, inferInstance⟩ n))
            (pushforward_idealPowerMultiple_comp_eq_zero f J (n + 1) _
              (completionProjection_idealPowerMultiple_comp (J.comap f)
                ⟨F, inferInstance⟩ n))) = _
  rw [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact cokernel.π_desc (C := Y.Modules) _ _ _

/-- **The comparison morphism of inverse systems.** Its component at `n` is
`Stacks.Coherent.pushforwardCompletionComponent`; naturality is checked after cancelling the
projection of `f_*𝓕`, which is an epimorphism. -/
public def pushforwardCompletionComparison {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (J : Y.IdealSheafData) (F : X.Modules) [F.IsCoherent]
    [((Scheme.Modules.pushforward f).obj F).IsCoherent] :
    ((Stacks.Algebraization.completionFunctor Y J).obj
      ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩).obj ⟶
      ((Stacks.Algebraization.completionFunctor X (J.comap f)).obj
        ⟨F, inferInstance⟩).obj ⋙ Scheme.Modules.pushforward f where
  app n := pushforwardCompletionComponent f J F n.unop
  naturality i j a := by
    let P : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf :=
      ⟨(Scheme.Modules.pushforward f).obj F, inferInstance⟩
    let Q : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf :=
      ⟨F, inferInstance⟩
    have := epi_completionProjection J P i.unop
    refine (cancel_epi (C := Y.Modules)
      (Stacks.Algebraization.completionProjection Y J P i.unop)).mp ?_
    have hY := Stacks.Algebraization.completionProjection_naturality J P a
    have hX := Stacks.Algebraization.completionProjection_naturality (J.comap f) Q a
    change Stacks.Algebraization.completionProjection Y J P i.unop ≫
      (((Stacks.Algebraization.completionFunctor Y J).obj P).obj.map a ≫
        pushforwardCompletionComponent f J F j.unop) =
      Stacks.Algebraization.completionProjection Y J P i.unop ≫
        (pushforwardCompletionComponent f J F i.unop ≫
          (Scheme.Modules.pushforward f).map
            (((Stacks.Algebraization.completionFunctor X (J.comap f)).obj Q).obj.map a))
    exact ((Category.assoc (obj := Y.Modules) _ _ _).symm.trans
        ((congrArg (· ≫ pushforwardCompletionComponent f J F j.unop) hY).trans
          ((pushforwardCompletionComponent_π f J F j.unop).trans
            ((congrArg (fun k => (Scheme.Modules.pushforward f).map k) hX.symm).trans
              ((Scheme.Modules.pushforward f).map_comp _ _))))).trans
      ((congrArg (· ≫ (Scheme.Modules.pushforward f).map
            (((Stacks.Algebraization.completionFunctor X (J.comap f)).obj Q).obj.map a))
          (pushforwardCompletionComponent_π f J F i.unop).symm).trans
        (Category.assoc (obj := Y.Modules) _ _ _))

/-- The component of the comparison morphism at `n` is the comparison map at level `n`. -/
public lemma pushforwardCompletionComparison_app {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (J : Y.IdealSheafData) (F : X.Modules) [F.IsCoherent]
    [((Scheme.Modules.pushforward f).obj F).IsCoherent] (n : ℕ) :
    (pushforwardCompletionComparison f J F).app (op n) =
      pushforwardCompletionComponent f J F n :=
  rfl

end Stacks.Coherent

end
