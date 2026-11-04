module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.KoszulComplex
public import StacksFrontier.LinearAlgebra.ExteriorPower.Koszul
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Koszul complex of a surjective étale cover resolves the constant sheaf

Let `X` be an algebraic space over a scheme `S` and let `U` be an algebraic space étale over
`X` whose structure morphism is surjective.  The augmentation `K^• ⟶ ℤ[0]` of the Koszul
complex of the trace `j_{U!} ℤ ⟶ ℤ` is then a quasi-isomorphism, so `K^•` is a resolution of
the constant sheaf of integers on the spaces-étale site of `X`.

## Main results

* `exteriorPower.contract_exact_of_apply_eq_one` and
  `exteriorPower.augmentation_exact_of_apply_eq_one`: a linear form taking the value `1` on
  some vector makes its augmented Koszul complex exact, the contracting homotopy of
  Stacks 0626 being left multiplication by that vector.
* `AlgebraicGeometry.Space.SpacesEtale.koszulAugmentation_quasiIso` is **Stacks 0723**: for `U`
  surjective over `X` the augmentation `K^• ⟶ ℤ[0]` is a quasi-isomorphism.

## Implementation notes

Exactness in positive degrees needs no surjectivity hypothesis, and is checked before
sheafification, objectwise on the spaces-étale site: over an object `V` admitting a morphism
to `U` the trace takes the value `1` on the generator of `j_{U!} ℤ` attached to that morphism,
so the Koszul complex of sections over `V` is contractible, while over an object admitting no
morphism to `U` the free abelian presheaf has no nonzero section and all the exterior powers
of positive degree vanish.  Sheafification is exact, so it carries these exact sequences of
presheaves to exact sequences of sheaves.

Surjectivity of `U ⟶ X` enters only through the augmentation in degree `0`: it makes the
single morphism from `U` to the final object of the spaces-étale site a covering, so every
object of the site is covered by objects admitting a morphism to `U`, over which the trace is
surjective.  Hence the augmentation is locally surjective, so an epimorphism after
sheafification.

## References

* [Stacks Project, Tag 0723](https://stacks.math.columbia.edu/tag/0723)
* [Stacks Project, Tag 0626](https://stacks.math.columbia.edu/tag/0626)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CliffordAlgebra ExteriorAlgebra Opposite

universe w v u

/-! ### The Koszul complex of a linear form of trace one is exact -/

namespace exteriorPower

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Left multiplication by a vector carries the `n`-th exterior power into the `(n+1)`-st. -/
theorem ι_mul_mem (e : M) (n : ℕ) {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^n M) :
    ι R e * x ∈ ⋀[R]^(n + 1) M := by
  show _ ∈ (LinearMap.range (ι R : M →ₗ[R] ExteriorAlgebra R M)) ^ (n + 1)
  rw [pow_succ' (LinearMap.range (ι R : M →ₗ[R] ExteriorAlgebra R M)) n]
  exact Submodule.mul_mem_mul ⟨e, rfl⟩ hx

/-- A member of the first exterior power is the image of the vector it corresponds to. -/
theorem coe_eq_ι_oneEquiv (y : ⋀[R]^1 M) :
    (y : ExteriorAlgebra R M) = ι R (oneEquiv R M y) := by
  conv_lhs => rw [← (oneEquiv R M).symm_apply_apply y]
  rw [oneEquiv_symm_apply]
  simp [ExteriorAlgebra.ιMulti_succ_apply]

/-- Contraction by a linear form vanishes on the zeroth exterior power, the scalars. -/
theorem contractLeft_coe_eq_zero_of_mem_zero {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^0 M)
    (d : Module.Dual R M) : contractLeft d x = 0 := by
  change x ∈ (LinearMap.range (ι R : M →ₗ[R] ExteriorAlgebra R M)) ^ 0 at hx
  rw [pow_zero] at hx
  obtain ⟨r, rfl⟩ := Submodule.mem_one.1 hx
  rw [contractLeft_algebraMap]

/-- Contraction by `d` and left multiplication by `e` form a homotopy for multiplication by
the scalar `d e` on the exterior powers: `d e • x = d(e ∧ x) + e ∧ d(x)`. -/
@[ega "III 1.1.7" "partial"]
theorem contract_wedgeLeft_add_wedgeLeft_contract (d : Module.Dual R M) (e : M) (n : ℕ)
    (x : ⋀[R]^(n + 1) M) :
    contract d (n + 1) (wedgeLeft e (n + 1) x) + wedgeLeft e n (contract d n x) = d e • x := by
  refine Subtype.ext ?_
  push_cast [Submodule.coe_add, coe_contract, coe_wedgeLeft, SetLike.val_smul]
  rw [contractLeft_ι_mul]
  abel

/-- Contraction into degree zero vanishes exactly when the linear form vanishes on the vector
corresponding to the given member of the first exterior power. -/
theorem contract_zero_eq_zero_iff (d : Module.Dual R M) (y : ⋀[R]^1 M) :
    contract d 0 y = 0 ↔ d (oneEquiv R M y) = 0 := by
  constructor
  · intro hy
    have h : (contract d 0 y : ExteriorAlgebra R M) = 0 := congrArg Subtype.val hy
    rw [coe_contract, coe_eq_ι_oneEquiv y, contractLeft_ι] at h
    exact (ExteriorAlgebra.algebraMap_eq_zero_iff M _).1 h
  · intro hy
    refine Subtype.ext ?_
    rw [coe_contract, coe_eq_ι_oneEquiv y, contractLeft_ι, hy, map_zero]
    rfl

/-- A linear form taking the value `1` on a vector `e` makes its Koszul complex exact: left
multiplication by `e` is a contracting homotopy, by the identity of Stacks 0626. -/
theorem contract_exact_of_apply_eq_one (d : Module.Dual R M) {e : M} (he : d e = 1) (n : ℕ) :
    Function.Exact (contract d (n + 1)) (contract d n) := by
  intro y
  refine ⟨fun hy => ⟨wedgeLeft e (n + 1) y, ?_⟩, ?_⟩
  · have h := contract_wedgeLeft_add_wedgeLeft_contract d e n y
    rwa [hy, map_zero, add_zero, he, one_smul] at h
  · rintro ⟨z, rfl⟩
    exact contract_contract d n z

/-- The augmented Koszul complex of a linear form taking the value `1` is exact at the first
exterior power, the augmentation being the form itself read through the identification of the
first exterior power with the module. -/
theorem augmentation_exact_of_apply_eq_one (d : Module.Dual R M) {e : M} (he : d e = 1) :
    Function.Exact (contract d 1) (d ∘ₗ (oneEquiv R M).toLinearMap) := by
  intro y
  refine ⟨fun hy => ⟨wedgeLeft e 1 y, ?_⟩, ?_⟩
  · have h := contract_wedgeLeft_add_wedgeLeft_contract d e 0 y
    rwa [(contract_zero_eq_zero_iff d y).2 hy, map_zero, add_zero, he, one_smul] at h
  · rintro ⟨z, rfl⟩
    exact apply_oneEquiv_contract_eq_zero d z

/-- The exterior powers of positive degree of a trivial module are trivial. -/
theorem subsingleton_of_subsingleton [Subsingleton M] (n : ℕ) :
    Subsingleton (⋀[R]^(n + 1) M) :=
  subsingleton_of_span_eq_top_of_card_lt (R := R) (fun i : Fin 0 => Fin.elim0 i)
    (Subsingleton.elim _ _) (n + 1) (by simp)

end exteriorPower

/-! ### Objectwise exactness of the Koszul complex of a presheaf -/

namespace AddCommGrpCat

variable {C : Type u} [Category.{v} C]

/-- A short complex of presheaves of abelian groups is exact as soon as it is exact at every
object of the index category. -/
theorem shortComplex_exact_of_evaluation (T : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat.{w}))
    (hT : ∀ V, (T.map ((evaluation Cᵒᵖ AddCommGrpCat.{w}).obj V)).Exact) : T.Exact := by
  rw [T.exact_iff_isZero_homology, Limits.IsZero.iff_id_eq_zero]
  refine NatTrans.ext (funext fun V => ?_)
  exact (((T.map ((evaluation Cᵒᵖ AddCommGrpCat.{w}).obj V)).exact_iff_isZero_homology.mp
    (hT V)).of_iso
      (T.mapHomologyIso ((evaluation Cᵒᵖ AddCommGrpCat.{w}).obj V)).symm).eq_of_src _ _

variable {F : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (ε : F ⟶ constantInt.{w} C)

/-- The augmentation of the Koszul complex of `ε` reads a member of the first exterior power
as a section of `F` and applies `ε` to it. -/
theorem presheafKoszulAugmentation_app_apply (V : Cᵒᵖ) (y : ⋀[ℤ]^1 (F.obj V)) :
    (presheafKoszulAugmentation ε).app V y = (ε.app V) (exteriorPower.oneEquiv ℤ (F.obj V) y) :=
  rfl

/-- Sections over an object on which the trace takes the value `1` give an exact sequence of
exterior powers: the Koszul complex of a form of trace one is exact. -/
theorem presheafKoszulDiff_exact_app_of_apply_eq_one (V : Cᵒᵖ) {e : F.obj V}
    (he : presheafDual ε V e = 1) (n : ℕ) :
    Function.Exact ((presheafKoszulDiff ε (n + 1)).app V) ((presheafKoszulDiff ε n).app V) :=
  exteriorPower.contract_exact_of_apply_eq_one (presheafDual ε V) he n

/-- The augmented Koszul complex of `ε` is exact at the first exterior power over an object on
which the trace takes the value `1`. -/
theorem presheafKoszulAugmentation_exact_app_of_apply_eq_one (V : Cᵒᵖ) {e : F.obj V}
    (he : presheafDual ε V e = 1) :
    Function.Exact ((presheafKoszulDiff ε 1).app V) ((presheafKoszulAugmentation ε).app V) := by
  refine Function.Exact.of_comp_of_mem_range (funext fun x => ?_) (fun x hx => ?_)
  · exact congrArg (fun k : ℤ => (ULift.up k : ULift.{w} ℤ))
      (exteriorPower.apply_oneEquiv_contract_eq_zero (presheafDual ε V) x)
  · refine exteriorPower.augmentation_exact_of_apply_eq_one (presheafDual ε V) he x |>.1 ?_
    have h : (ε.app V) (exteriorPower.oneEquiv ℤ (F.obj V) x) = 0 := by
      rw [← presheafKoszulAugmentation_app_apply ε V x, hx]
    exact congrArg (fun z : ULift.{w} ℤ => z.down) h

/-- A pair of zero-preserving maps through a subsingleton is exact. -/
private theorem function_exact_of_subsingleton {A B C : Type*} [Zero A] [Zero B] [Zero C]
    [Subsingleton B] {f : A → B} {g : B → C} (hf : f 0 = 0) (hg : g 0 = 0) :
    Function.Exact f g := by
  intro y
  rw [Subsingleton.elim y 0]
  exact ⟨fun _ => ⟨0, hf⟩, fun _ => hg⟩

/-- The Koszul complex of `ε` is exact at every exterior power of positive degree over an
object whose sections of `F` are all zero. -/
theorem presheafKoszulDiff_exact_app_of_subsingleton (V : Cᵒᵖ)
    (hs : Subsingleton (F.obj V)) (n : ℕ) :
    Function.Exact ((presheafKoszulDiff ε (n + 1)).app V) ((presheafKoszulDiff ε n).app V) :=
  have : Subsingleton ((presheafExteriorPower F (n + 1)).obj V) :=
    exteriorPower.subsingleton_of_subsingleton (R := ℤ) (M := F.obj V) n
  function_exact_of_subsingleton (map_zero _) (map_zero _)

/-- The augmented Koszul complex of `ε` is exact at the first exterior power over an object
whose sections of `F` are all zero. -/
theorem presheafKoszulAugmentation_exact_app_of_subsingleton (V : Cᵒᵖ)
    (hs : Subsingleton (F.obj V)) :
    Function.Exact ((presheafKoszulDiff ε 1).app V) ((presheafKoszulAugmentation ε).app V) :=
  have : Subsingleton ((presheafExteriorPower F 1).obj V) :=
    exteriorPower.subsingleton_of_subsingleton (R := ℤ) (M := F.obj V) 0
  function_exact_of_subsingleton (map_zero _) (map_zero _)

/-- Over an object on which the trace takes the value `1` the augmentation of the Koszul
complex of `ε` is surjective. -/
theorem presheafKoszulAugmentation_surjective_app (V : Cᵒᵖ) {e : F.obj V}
    (he : presheafDual ε V e = 1) :
    Function.Surjective ((presheafKoszulAugmentation ε).app V) := by
  intro z
  refine ⟨(exteriorPower.oneEquiv ℤ (F.obj V)).symm (z.down • e), ?_⟩
  rw [presheafKoszulAugmentation_app_apply, LinearEquiv.apply_symm_apply]
  have h : presheafDual ε V (z.down • e) = z.down := by
    rw [map_zsmul, he, smul_eq_mul, mul_one]
  exact ULift.ext _ _ h

end AddCommGrpCat

/-! ### Exactness of the Koszul complex of a surjective étale cover -/

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- Over an object of the spaces-étale site of `X` admitting a morphism to `U`, the trace of
the free abelian presheaf on `U` takes the value `1`. -/
theorem exists_presheafDual_freeAbelianRepresentableTrace_eq_one (U : SpacesEtale B S hS X)
    (V : (SpacesEtale B S hS X)ᵒᵖ) (φ : V.unop ⟶ U) :
    ∃ e : (freeAbelianRepresentablePresheaf B S hS X U).obj V,
      AddCommGrpCat.presheafDual (freeAbelianRepresentableTrace B S hS X U) V e = 1 :=
  ⟨FreeAbelianGroup.of φ, presheafDual_freeAbelianRepresentableTrace_of B S hS X U V φ⟩

/-- Over an object of the spaces-étale site of `X` admitting no morphism to `U`, the free
abelian presheaf on `U` has no nonzero section. -/
theorem subsingleton_freeAbelianRepresentablePresheaf (U : SpacesEtale B S hS X)
    (V : (SpacesEtale B S hS X)ᵒᵖ) (h : IsEmpty (V.unop ⟶ U)) :
    Subsingleton ((freeAbelianRepresentablePresheaf B S hS X U).obj V) := by
  have hzero : ∀ x : FreeAbelianGroup (V.unop ⟶ U), x = 0 := by
    intro x
    induction x using FreeAbelianGroup.induction_on with
    | zero => rfl
    | of a => exact h.elim a
    | neg a _ => exact h.elim a
    | add y z hy hz => rw [hy, hz, add_zero]
  exact ⟨fun a b => (hzero a).trans (hzero b).symm⟩

/-- Over an object of the spaces-étale site of `X`, either the free abelian presheaf on `U` has
no nonzero section, or the trace takes the value `1` on some section. -/
private theorem subsingleton_or_exists_presheafDual_eq_one (U : SpacesEtale B S hS X)
    (V : (SpacesEtale B S hS X)ᵒᵖ) :
    Subsingleton ((freeAbelianRepresentablePresheaf B S hS X U).obj V) ∨
      ∃ e : (freeAbelianRepresentablePresheaf B S hS X U).obj V,
        AddCommGrpCat.presheafDual (freeAbelianRepresentableTrace B S hS X U) V e = 1 := by
  rcases isEmpty_or_nonempty (V.unop ⟶ U) with h | h
  · exact .inl (subsingleton_freeAbelianRepresentablePresheaf B S hS X U V h)
  · obtain ⟨φ⟩ := h
    exact .inr (exists_presheafDual_freeAbelianRepresentableTrace_eq_one B S hS X U V φ)

/-- Over every object of the spaces-étale site of `X` the Koszul complex of the trace of the
free abelian presheaf on `U` is exact in positive degrees, with no surjectivity hypothesis on
`U`: either the object admits a morphism to `U`, and then the trace takes the value `1`, or it
does not, and then the exterior powers of positive degree vanish. -/
theorem presheafKoszulDiff_exact_app (U : SpacesEtale B S hS X)
    (V : (SpacesEtale B S hS X)ᵒᵖ) (n : ℕ) :
    Function.Exact
      ((AddCommGrpCat.presheafKoszulDiff
        (freeAbelianRepresentableTrace B S hS X U) (n + 1)).app V)
      ((AddCommGrpCat.presheafKoszulDiff
        (freeAbelianRepresentableTrace B S hS X U) n).app V) := by
  rcases subsingleton_or_exists_presheafDual_eq_one B S hS X U V with h | ⟨e, he⟩
  · exact AddCommGrpCat.presheafKoszulDiff_exact_app_of_subsingleton _ V h n
  · exact AddCommGrpCat.presheafKoszulDiff_exact_app_of_apply_eq_one _ V he n

/-- Over every object of the spaces-étale site of `X` the augmented Koszul complex of the
trace is exact at the first exterior power, with no surjectivity hypothesis on `U`. -/
theorem presheafKoszulAugmentation_exact_app (U : SpacesEtale B S hS X)
    (V : (SpacesEtale B S hS X)ᵒᵖ) :
    Function.Exact
      ((AddCommGrpCat.presheafKoszulDiff (freeAbelianRepresentableTrace B S hS X U) 1).app V)
      ((AddCommGrpCat.presheafKoszulAugmentation
        (freeAbelianRepresentableTrace B S hS X U)).app V) := by
  rcases subsingleton_or_exists_presheafDual_eq_one B S hS X U V with h | ⟨e, he⟩
  · exact AddCommGrpCat.presheafKoszulAugmentation_exact_app_of_subsingleton _ V h
  · exact AddCommGrpCat.presheafKoszulAugmentation_exact_app_of_apply_eq_one _ V he

/-- The Koszul differentials of the trace form exact sequences of presheaves in positive
degrees. -/
theorem presheafKoszulDiff_shortComplex_exact (U : SpacesEtale B S hS X) (n : ℕ) :
    (ShortComplex.mk
      (AddCommGrpCat.presheafKoszulDiff (freeAbelianRepresentableTrace B S hS X U) (n + 1))
      (AddCommGrpCat.presheafKoszulDiff (freeAbelianRepresentableTrace B S hS X U) n)
      (AddCommGrpCat.presheafKoszulDiff_comp
        (freeAbelianRepresentableTrace B S hS X U) n)).Exact :=
  AddCommGrpCat.shortComplex_exact_of_evaluation _ fun V =>
    (ShortComplex.ab_exact_iff_function_exact _).2
      (presheafKoszulDiff_exact_app B S hS X U V n)

/-- The first Koszul differential of the trace and the augmentation form an exact sequence of
presheaves. -/
theorem presheafKoszulAugmentation_shortComplex_exact (U : SpacesEtale B S hS X) :
    (ShortComplex.mk
      (AddCommGrpCat.presheafKoszulDiff (freeAbelianRepresentableTrace B S hS X U) 1)
      (AddCommGrpCat.presheafKoszulAugmentation (freeAbelianRepresentableTrace B S hS X U))
      (AddCommGrpCat.presheafKoszulDiff_comp_presheafKoszulAugmentation
        (freeAbelianRepresentableTrace B S hS X U))).Exact :=
  AddCommGrpCat.shortComplex_exact_of_evaluation _ fun V =>
    (ShortComplex.ab_exact_iff_function_exact _).2
      (presheafKoszulAugmentation_exact_app B S hS X U V)

/-- The complex `K^•` is exact in positive degrees: sheafification is exact, so it carries the
objectwise exact sequences of exterior powers to exact sequences of sheaves. -/
theorem koszulComplex_exactAt_succ (U : SpacesEtale B S hS X) (n : ℕ) :
    (koszulComplex B S hS X U).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n
    ((ComplexShape.down ℕ).prev_eq' rfl) ((ComplexShape.down ℕ).next_eq' rfl)]
  have h := (presheafKoszulDiff_shortComplex_exact B S hS X U (n + 1)).map
    (presheafToSheaf (topology B S hS X) AddCommGrpCat.{u + 1})
  refine (ShortComplex.exact_iff_of_iso ?_).2 h
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans
      ((koszulComplex_d B S hS X U (n + 1)).symm.trans (Category.comp_id _).symm))
    ((Category.id_comp _).trans
      ((koszulComplex_d B S hS X U n).symm.trans (Category.comp_id _).symm))

/-- The first differential of `K^•` and the trace `K^0 ⟶ ℤ` form an exact sequence of
sheaves. -/
theorem koszulTrace_shortComplex_exact (U : SpacesEtale B S hS X) :
    (ShortComplex.mk ((koszulComplex B S hS X U).d 1 0) (koszulTrace B S hS X U)
      (koszulComplex_d_comp_koszulTrace B S hS X U)).Exact := by
  have h := (presheafKoszulAugmentation_shortComplex_exact B S hS X U).map
    (presheafToSheaf (topology B S hS X) AddCommGrpCat.{u + 1})
  refine (ShortComplex.exact_iff_of_iso ?_).2 h
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans
      ((koszulComplex_d B S hS X U 0).symm.trans (Category.comp_id _).symm))
    ((Category.id_comp _).trans (Category.comp_id _).symm)

/-! ### Surjectivity of the trace for a surjective cover -/

/-- The underlying morphism of algebraic spaces of the unique morphism from `U` to the final
object of the spaces-étale site of `X` is the structure morphism of `U`. -/
theorem toSpaces_map_default_toFinal (U : SpacesEtale B S hS X) :
    (toSpaces B S hS X).map (default : U ⟶ final B S hS X) = U.obj.hom :=
  Over.mkIdTerminal_from_left U.obj

/-- If the structure morphism of `U` is surjective then the single morphism from `U` to the
final object of the spaces-étale site of `X` is a covering. -/
theorem sieve₀_singleton_mem_topology (U : SpacesEtale B S hS X)
    (hsurj : IsSurjective B S hS U.obj.hom.hom) :
    (PreZeroHypercover.singleton.{u + 1}
      (default : U ⟶ final B S hS X)).sieve₀ ∈ topology B S hS X (final B S hS X) := by
  apply Precoverage.generate_mem_toGrothendieck
  refine ⟨PreZeroHypercover.singleton _, rfl, fun x => ?_⟩
  obtain ⟨y, hy⟩ := hsurj x
  refine ⟨PUnit.unit, y, ?_⟩
  have h : ((toSpaces B S hS X).map (default : U ⟶ final B S hS X)).hom = U.obj.hom.hom :=
    congrArg (fun k : (toSpaces B S hS X).obj U ⟶ X => k.hom)
      (toSpaces_map_default_toFinal B S hS X U)
  exact (congrArg (fun k : ((toSpaces B S hS X).obj U).obj ⟶ X.obj =>
    pointsMap B S hS ((toSpaces B S hS X).obj U).obj k y) h).trans hy

/-- For a surjective `U` the augmentation of the Koszul presheaf is locally surjective: every
object of the spaces-étale site of `X` is covered by its pullback to `U`, over which the trace
is surjective. -/
theorem presheafKoszulAugmentation_isLocallySurjective (U : SpacesEtale B S hS X)
    (hsurj : IsSurjective B S hS U.obj.hom.hom) :
    Presheaf.IsLocallySurjective (topology B S hS X)
      (AddCommGrpCat.presheafKoszulAugmentation
        (freeAbelianRepresentableTrace B S hS X U)) where
  imageSieve_mem {V} x := by
    refine (topology B S hS X).superset_covering ?_
      ((topology B S hS X).pullback_stable (default : V ⟶ final B S hS X)
        (sieve₀_singleton_mem_topology B S hS X U hsurj))
    rintro W k ⟨Z, g, t, ⟨i⟩, -⟩
    exact AddCommGrpCat.presheafKoszulAugmentation_surjective_app _ (op W)
      (presheafDual_freeAbelianRepresentableTrace_of B S hS X U (op W) g) _

/-- For a surjective `U` the trace `K^0 ⟶ ℤ` is an epimorphism of sheaves. -/
theorem epi_koszulTrace (U : SpacesEtale B S hS X)
    (hsurj : IsSurjective B S hS U.obj.hom.hom) : Epi (koszulTrace B S hS X U) := by
  have h : Sheaf.IsLocallySurjective
      ((presheafToSheaf (topology B S hS X) AddCommGrpCat.{u + 1}).map
        (AddCommGrpCat.presheafKoszulAugmentation
          (freeAbelianRepresentableTrace B S hS X U))) :=
    (Presheaf.isLocallySurjective_presheafToSheaf_map_iff _ _).2
      (presheafKoszulAugmentation_isLocallySurjective B S hS X U hsurj)
  exact (Sheaf.isLocallySurjective_iff_epi' _ _).1 h

/-- **Stacks 0723.** For an algebraic space `U` étale and surjective over `X`, the augmentation
`K^• ⟶ ℤ[0]` of the Koszul complex of the trace `j_{U!} ℤ ⟶ ℤ` is a quasi-isomorphism: `K^•`
is a resolution of the constant sheaf `ℤ` on the spaces-étale site of `X`. -/
@[stacks 0723 "the augmentation is a quasi-isomorphism for a surjective cover"]
theorem koszulAugmentation_quasiIso (U : SpacesEtale B S hS X)
    (hsurj : IsSurjective B S hS U.obj.hom.hom) :
    QuasiIso (koszulAugmentation B S hS X U) := by
  refine ⟨fun n => ?_⟩
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · refine ⟨?_, ?_⟩
      · refine (ShortComplex.exact_iff_of_iso ?_).2
          (koszulTrace_shortComplex_exact B S hS X U)
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          ((Category.id_comp _).trans (Category.comp_id _).symm)
          ((Category.id_comp _).trans
            ((koszulAugmentation_f_zero_eq B S hS X U).symm.trans (Category.comp_id _).symm))
      · have hepi := epi_koszulTrace B S hS X U hsurj
        rwa [← koszulAugmentation_f_zero_eq B S hS X U] at hepi
    · exact (koszulComplex B S hS X U).shape 0 0 (by simp)
    · rfl
    · rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt']
    · exact koszulComplex_exactAt_succ B S hS X U n
    · exact HomologicalComplex.exactAt_single_obj _ _ _ _ (Nat.succ_ne_zero n)

end AlgebraicGeometry.Space.SpacesEtale

end
