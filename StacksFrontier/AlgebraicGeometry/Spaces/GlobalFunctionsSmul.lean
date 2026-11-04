module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GlobalFunctionsAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction

/-!
# Multiplication by a global regular function on `𝒪_X`-modules

Let `X` be an algebraic space and `s ∈ Γ(X, 𝒪_X)` a global regular function
(`AlgebraicGeometry.Space.globalFunctions'`, the compatible families of regular functions on the
étale charts of `X`). Multiplication by `s` is an endomorphism of every `𝒪_X`-module `N`: on the
sections over an étale chart `U` it is multiplication by the restriction `s|_U ∈ Γ(U, 𝒪_U)`
(`AlgebraicGeometry.Space.globalFunctionsSmul`). It commutes with every morphism of
`𝒪_X`-modules, is a ring homomorphism into the endomorphisms, and is carried by the inverse image
along an étale morphism `f : Y ⟶ X` of Stacks 03LU to multiplication by the pulled back function
`f^*s` (`AlgebraicGeometry.Space.modulePullback_map_globalFunctionsSmul`), through the
identification of Stacks 03LW of that inverse image with étale restriction.

These are the scalars of the `Γ(U, 𝒪_U)`-module structure on `Hom_{𝒪_U}(Δ^*Ω, 𝒞)` in the proof of
Stacks 0CKG (2).

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 0CKG](https://stacks.math.columbia.edu/tag/0CKG)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Smul

variable {X : AlgebraicSpaces B S hS}

/-- The restriction `s|_U` of a global regular function to an étale chart, as an element of the
structure ring of the chart. -/
abbrev globalFunctionsAt (s : globalFunctions' B S hS X.1) (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj U :=
  s.val U

/-- The restrictions of a global regular function to étale charts are compatible with the
restriction maps of the structure sheaf: `(s|_U)|_V = s|_V` for `g : U ⟶ V`. -/
theorem globalFunctionsAt_map (s : globalFunctions' B S hS X.1) {U V : (SmallEtale B S hS X.1)ᵒᵖ}
    (g : U ⟶ V) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.map
        g (globalFunctionsAt B S hS s U) = globalFunctionsAt B S hS s V :=
  s.property g

/-- Multiplication by `s|_U` on the sections over `U` of an `𝒪_X`-module, as a linear map. -/
def globalFunctionsSmulApp (s : globalFunctions' B S hS X.1) (N : Modules.{u, m} B S hS X.1 X.2)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) : N.val.obj U ⟶ N.val.obj U :=
  ModuleCat.ofHom
    { toFun := fun x => globalFunctionsAt B S hS s U • x
      map_add' := fun x y => smul_add _ x y
      map_smul' := fun r x => by
        change globalFunctionsAt B S hS s U • r • x = r • globalFunctionsAt B S hS s U • x
        rw [smul_smul, smul_smul]
        congr 1
        exact mul_comm (G := ((structurePresheaf B S hS X.1).obj U)) _ _ }

/-- `globalFunctionsSmulApp s N U` sends a section `x` to `s|_U • x`. -/
theorem globalFunctionsSmulApp_apply (s : globalFunctions' B S hS X.1)
    (N : Modules.{u, m} B S hS X.1 X.2) (U : (SmallEtale B S hS X.1)ᵒᵖ) (x : N.val.obj U) :
    globalFunctionsSmulApp B S hS s N U x = globalFunctionsAt B S hS s U • x :=
  rfl

/-- **Multiplication by a global regular function** on an `𝒪_X`-module: on the sections over an
étale chart `U`, multiplication by the restriction `s|_U`. -/
def globalFunctionsSmul (s : globalFunctions' B S hS X.1) (N : Modules.{u, m} B S hS X.1 X.2) :
    N ⟶ N where
  val :=
    { app := globalFunctionsSmulApp B S hS s N
      naturality := fun {U V} g => by
        ext x
        exact ((PresheafOfModules.map_smul N.val g (globalFunctionsAt B S hS s U) x).trans
          (congrArg (· • N.val.map g x) (globalFunctionsAt_map B S hS s g))).symm }

/-- On the sections over an étale chart `U`, `globalFunctionsSmul s N` sends `x` to `s|_U • x`. -/
theorem globalFunctionsSmul_val_app_apply (s : globalFunctions' B S hS X.1)
    (N : Modules.{u, m} B S hS X.1 X.2) (U : (SmallEtale B S hS X.1)ᵒᵖ) (x : N.val.obj U) :
    (globalFunctionsSmul B S hS s N).val.app U x = globalFunctionsAt B S hS s U • x :=
  rfl

/-- Multiplication by a global regular function commutes with every morphism of modules. -/
@[reassoc]
theorem comp_globalFunctionsSmul (s : globalFunctions' B S hS X.1)
    {N N' : Modules.{u, m} B S hS X.1 X.2} (φ : N ⟶ N') :
    φ ≫ globalFunctionsSmul B S hS s N' = globalFunctionsSmul B S hS s N ≫ φ := by
  ext U x
  show globalFunctionsAt B S hS s U • φ.val.app U x =
    φ.val.app U (globalFunctionsAt B S hS s U • x)
  exact (map_smul (φ.val.app U).hom _ x).symm

/-- Multiplication by the global function `1` is the identity. -/
theorem globalFunctionsSmul_one (N : Modules.{u, m} B S hS X.1 X.2) :
    globalFunctionsSmul B S hS 1 N = 𝟙 N := by
  ext U x
  exact one_smul _ x

/-- Multiplication by the global function `0` is the zero morphism. -/
theorem globalFunctionsSmul_zero (N : Modules.{u, m} B S hS X.1 X.2) :
    globalFunctionsSmul B S hS 0 N = 0 := by
  ext U x
  exact zero_smul _ x

/-- Multiplication by `s + t` is the sum of multiplication by `s` and multiplication by `t`. -/
theorem globalFunctionsSmul_add (s t : globalFunctions' B S hS X.1)
    (N : Modules.{u, m} B S hS X.1 X.2) :
    globalFunctionsSmul B S hS (s + t) N =
      globalFunctionsSmul B S hS s N + globalFunctionsSmul B S hS t N := by
  ext U x
  exact add_smul _ _ x

/-- Multiplication by `s * t` is multiplication by `t` followed by multiplication by `s`. -/
theorem globalFunctionsSmul_mul (s t : globalFunctions' B S hS X.1)
    (N : Modules.{u, m} B S hS X.1 X.2) :
    globalFunctionsSmul B S hS (s * t) N =
      globalFunctionsSmul B S hS t N ≫ globalFunctionsSmul B S hS s N := by
  ext U x
  exact mul_smul _ _ x

end Smul

section Etale

variable {X Y : AlgebraicSpaces B S hS}

/-- **The pullback of a global regular function along an étale morphism, on an étale chart**, is
its value on the composite chart. -/
theorem globalFunctionsMap_val_of_isEtale (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (s : globalFunctions' B S hS X.1) (U : (SmallEtale B S hS Y.1)ᵒᵖ) :
    (globalFunctionsMap B S hS f s).val U =
      s.val (op ((smallEtalePostcomp B S hS f hf).obj U.unop)) := by
  have h := congrArg (fun t => (chartFunctionsToSmall B S hS Y.1 t).val U)
    (globalFunctionsMap_chart B S hS f s)
  rw [(globalFunctionsChartEquiv B S hS Y).2] at h
  refine h.trans ?_
  show ((globalFunctionsChartEquiv B S hS X).val s).val
      ((CostructuredArrow.map f.hom).op.obj ((SmallEtale.inclusion B S hS Y.1).op.obj U)) = _
  exact congrArg (fun t => t.val (op ((smallEtalePostcomp B S hS f hf).obj U.unop)))
    ((globalFunctionsChartEquiv B S hS X).2 s)

/-- Étale restriction carries multiplication by `s` to multiplication by `f^*s`. -/
theorem etaleModulePullback_map_globalFunctionsSmul (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (s : globalFunctions' B S hS X.1) (N : Modules.{u, m} B S hS X.1 X.2) :
    (etaleModulePullback B S hS f hf).map (globalFunctionsSmul B S hS s N) =
      globalFunctionsSmul B S hS (globalFunctionsMap B S hS f s)
        ((etaleModulePullback B S hS f hf).obj N) := by
  ext U x
  show (globalFunctionsSmul B S hS s N).val.app
      (op ((smallEtalePostcomp B S hS f hf).obj U.unop)) x =
    globalFunctionsAt B S hS (globalFunctionsMap B S hS f s) U • x
  have hb : globalFunctionsAt B S hS (globalFunctionsMap B S hS f s) U =
      globalFunctionsAt B S hS s (op ((smallEtalePostcomp B S hS f hf).obj U.unop)) :=
    globalFunctionsMap_val_of_isEtale B S hS f hf s U
  rw [hb]
  rfl

/-- **The inverse image of Stacks 03LU along an étale morphism carries multiplication by `s` to
multiplication by `f^*s`.** -/
theorem modulePullback_map_globalFunctionsSmul (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (s : globalFunctions' B S hS X.1) (N : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS f).map (globalFunctionsSmul B S hS s N) =
      globalFunctionsSmul B S hS (globalFunctionsMap B S hS f s)
        ((modulePullback B S hS f).obj N) := by
  let e := modulePullbackIsoEtaleModulePullback B S hS f hf
  have h := e.hom.naturality (globalFunctionsSmul B S hS s N)
  rw [etaleModulePullback_map_globalFunctionsSmul B S hS f hf,
    comp_globalFunctionsSmul] at h
  rw [← cancel_mono (e.hom.app N), h]

end Etale

end AlgebraicGeometry.Space
