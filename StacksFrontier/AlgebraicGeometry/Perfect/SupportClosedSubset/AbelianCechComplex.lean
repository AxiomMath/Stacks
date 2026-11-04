module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AbelianFractionFunctoriality
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedFractionMap

/-!
# Functoriality of the extended alternating Čech complex in abelian sheaves

Let `X` be a scheme and let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` be global functions. The extended
alternating Čech complex

`ℱ ⟶ ⨁ᵢ ℱ_i ⟶ ⨁_{i < j} ℱ_{ij} ⟶ ⋯ ⟶ ℱ_{1…c}`

is `Stacks.Perfect.ExtendedAlternatingCech.cplx`, a cochain complex of sheaves of `𝒪_X`-modules.
After forgetting to sheaves of abelian groups, it is functorial in `ℱ` along an arbitrary morphism
of the underlying presheaves of abelian groups, not only along morphisms of `𝒪_X`-modules.

## Main definitions

* `Stacks.Perfect.AbelianFraction.cplxAb`: the map of cochain complexes of sheaves of abelian
  groups induced on the extended alternating Čech complex by a morphism of the underlying
  presheaves of abelian groups of the coefficient modules.

## Main results

* `Stacks.Perfect.AbelianFraction.map_dif_comp_termAb`: every differential of the extended
  alternating Čech complex commutes with the induced map on terms;
  `Stacks.Perfect.AbelianFraction.map_cplx_d_comp_termAb` is the same statement with the
  differential written as that of the complex.
* `Stacks.Perfect.AbelianFraction.cplxAb_f`: the degree-`n` component of `cplxAb` is `termAb`.
* `Stacks.Perfect.AbelianFraction.cplxAb_mapPresheaf`: on a morphism of `X.Modules`, `cplxAb` is
  the image of `Stacks.Perfect.ExtendedAlternatingCech.cplxMap` under the forgetful functor.
* `Stacks.Perfect.AbelianFraction.cplxAb_id`, `Stacks.Perfect.AbelianFraction.termAb_comp` and
  `Stacks.Perfect.AbelianFraction.cplxAb_comp`: unitality and compatibility with composition.
* `Stacks.Perfect.AbelianFraction.map_lastDif_comp_cplxAb_f`: the naturality square of the last
  differential is the square `cplxAb` carries in the top two degrees.

## References

* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Perfect.ExtendedAlternatingCech
open Stacks.Perfect.SupportedFraction
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.AbelianFraction

variable {X : Scheme.{u}} {F G H : X.Modules}

/-! ### The differentials commute with the induced maps on terms -/

section Terms

variable {c : ℕ} (f : Fin c → Γ(X, ⊤))

/-- Two morphisms of sheaves of abelian groups on `X` agree if they agree on all sections. -/
private theorem sheaf_hom_ext_apply
    {A B : Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}} {a b : A ⟶ B}
    (h : ∀ (U : X.Opens) (x : A.obj.obj (op U)),
      (a.hom.app (op U)).hom x = (b.hom.app (op U)).hom x) :
    a = b :=
  Sheaf.hom_ext (NatTrans.ext (funext fun U =>
    AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => h U.unop x)))

/-- **Every differential of the extended alternating Čech complex commutes with the map induced
on its terms by a morphism of the underlying presheaves of abelian groups.** -/
public theorem map_dif_comp_termAb (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)
    (n : ℕ) :
    (abelianSheaf X).map (dif f F n) ≫ termAb f ψ (n + 1) =
      termAb f ψ n ≫ (abelianSheaf X).map (dif f G n) := by
  refine sheaf_hom_ext_apply fun U x => ?_
  cases n with
  | zero => exact prodTermAbApp_difZero f ψ U x
  | succ p => exact prodTermAbApp_difSucc f ψ p U x

/-- The naturality square of `map_dif_comp_termAb`, with the differential written as that of the
complex `Stacks.Perfect.ExtendedAlternatingCech.cplx`. -/
public theorem map_cplx_d_comp_termAb
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) (n : ℕ) :
    (abelianSheaf X).map ((cplx f F).d n (n + 1)) ≫ termAb f ψ (n + 1) =
      termAb f ψ n ≫ (abelianSheaf X).map ((cplx f G).d n (n + 1)) := by
  rw [show (cplx f F).d n (n + 1) = dif f F n from CochainComplex.of_d (term f F) (dif f F) n,
    show (cplx f G).d n (n + 1) = dif f G n from CochainComplex.of_d (term f G) (dif f G) n]
  exact map_dif_comp_termAb f ψ n

/-! ### The induced map of cochain complexes -/

/-- **The map of cochain complexes of sheaves of abelian groups induced on the extended
alternating Čech complex by a morphism of the underlying presheaves of abelian groups of the
coefficient modules.** Its degree-`n` component is `Stacks.Perfect.AbelianFraction.termAb`. -/
public def cplxAb (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    ((abelianSheaf X).mapHomologicalComplex (ComplexShape.up ℕ)).obj (cplx f F) ⟶
      ((abelianSheaf X).mapHomologicalComplex (ComplexShape.up ℕ)).obj (cplx f G) where
  f n := termAb f ψ n
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    exact (map_cplx_d_comp_termAb f ψ i).symm

/-- The degree-`n` component of `cplxAb` is the induced map on the degree-`n` Čech term. -/
public theorem cplxAb_f (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) (n : ℕ) :
    (cplxAb f ψ).f n = termAb f ψ n := rfl

/-- **The abelian functoriality of the complex extends the `𝒪_X`-linear one.** On the underlying
morphism of presheaves of a morphism of `X.Modules`, `cplxAb` is the image under the forgetful
functor of the chain map `Stacks.Perfect.ExtendedAlternatingCech.cplxMap`. -/
public theorem cplxAb_mapPresheaf (φ : F ⟶ G) :
    cplxAb f (Scheme.Modules.Hom.mapPresheaf φ) =
      ((abelianSheaf X).mapHomologicalComplex (ComplexShape.up ℕ)).map (cplxMap f φ) :=
  HomologicalComplex.hom_ext _ _ fun n => termAb_mapPresheaf f φ n

/-- The chain map induced by the identity of the coefficient module is the identity. -/
private theorem cplxMap_id_eq (F : X.Modules) : cplxMap f (𝟙 F) = 𝟙 (cplx f F) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  cases n with
  | zero => rfl
  | succ p => exact prodMap_id f F p

/-- The induced map of complexes belonging to the identity is the identity. -/
public theorem cplxAb_id :
    cplxAb f (Scheme.Modules.Hom.mapPresheaf (𝟙 F)) = 𝟙 _ := by
  rw [cplxAb_mapPresheaf, cplxMap_id_eq, CategoryTheory.Functor.map_id]

/-- The induced map on the sections of a positive-degree Čech term is compatible with composition
of morphisms of the underlying presheaves of abelian groups. -/
private theorem prodTermAbApp_comp
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)
    (χ : Scheme.Modules.presheaf G ⟶ Scheme.Modules.presheaf H) (p : ℕ) (V : X.Opens)
    (x : Γ(prodTerm f F p, V)) :
    prodTermAbApp f (ψ ≫ χ) p V x =
      prodTermAbApp f χ p V (prodTermAbApp f ψ p V x) := by
  refine (secIso f H p V).injective (funext fun s => ?_)
  rw [secIso_prodTermAbApp, secIso_prodTermAbApp, secIso_prodTermAbApp]
  rfl

/-- The induced map on an arbitrary Čech term is compatible with composition of morphisms of the
underlying presheaves of abelian groups. -/
public theorem termAb_comp (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)
    (χ : Scheme.Modules.presheaf G ⟶ Scheme.Modules.presheaf H) (n : ℕ) :
    termAb f (ψ ≫ χ) n = termAb f ψ n ≫ termAb f χ n := by
  refine sheaf_hom_ext_apply fun U x => ?_
  cases n with
  | zero => rfl
  | succ p => exact prodTermAbApp_comp f ψ χ p U x

/-- The induced map of complexes is compatible with composition of morphisms of the underlying
presheaves of abelian groups. -/
public theorem cplxAb_comp (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)
    (χ : Scheme.Modules.presheaf G ⟶ Scheme.Modules.presheaf H) :
    cplxAb f (ψ ≫ χ) = cplxAb f ψ ≫ cplxAb f χ :=
  HomologicalComplex.hom_ext _ _ fun n => termAb_comp f ψ χ n

end Terms

/-! ### The last naturality square and the cokernel -/

section LastDif

variable {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤))

/-- **The naturality square of the last differential is the one carried by `cplxAb`**: the
components of `cplxAb` in the top two degrees commute with the last differentials
`Stacks.Perfect.SupportedFraction.lastDif`. -/
public theorem map_lastDif_comp_cplxAb_f
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    (abelianSheaf X).map (lastDif f F) ≫ (cplxAb f ψ).f (d + 1) =
      (cplxAb f ψ).f d ≫ (abelianSheaf X).map (lastDif f G) := by
  have h := (cplxAb f ψ).comm d (d + 1)
  rw [CategoryTheory.Functor.mapHomologicalComplex_obj_d,
    CategoryTheory.Functor.mapHomologicalComplex_obj_d, cplx_d_lastDif, cplx_d_lastDif] at h
  exact h.symm

end LastDif

end Stacks.Perfect.AbelianFraction

end
