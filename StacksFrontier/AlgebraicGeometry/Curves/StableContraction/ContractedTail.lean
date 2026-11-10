module

public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.StableModel
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.Iterated
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.AmpleNoRationalTail
public import StacksFrontier.AlgebraicGeometry.IdealPowerMultipleComparison.Algebraization
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ContractedDegree
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Contraction
public import StacksFrontier.AlgebraicGeometry.SheafPushforward.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleFactorThru
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.IdealPowerComplement.Basic

/-!
# A stable contraction contracts every rational tail

Let `X` be a proper nodal curve over a field `k` with `H⁰(X, 𝒪_X) = k`, let `C` be a rational tail
of `X` with attaching point `x` and let `X'` be the closure of its complement. For a morphism
`c : X ⟶ Y` with `𝒪_Y = c_*𝒪_X` this file computes the Euler characteristic of the ideal `𝓘` of
the scheme-theoretic image of `X'`: it is the direct image of the ideal `𝓙 𝒪_X` of `X'`, which is
in turn the direct image from `C` of the ideal of the attaching point, whence `χ(Y, 𝓘) = 0`. This
is the cohomological input of the step of [Stacks, Tag 0E7Q] showing that a stable contraction
maps `C` to a point.

## Main results

* `Stacks.Curves.StableModel.mem_idealPowerMultiple_unit_iff_app_eq_zero`: a section of `𝒪_X`
  lies in `I 𝒪_X` exactly when it restricts to zero on the subscheme cut out by `I`.
* `Stacks.Curves.StableModel.exists_idealPowerMultiple_ker_iso_pushforward`: for `𝒪_Y = c_*𝒪_X`,
  the ideal of the scheme-theoretic image of a closed subscheme of `X` is the direct image of its
  ideal.
* `Stacks.Curves.StableModel.finsum_finrank_cohomologyOverField_add_of_shortExact`: additivity of
  `χ` on a curve.
* `Stacks.Curves.StableModel.finsum_idealPowerMultiple_ker_inclusion_eq_zero`: the ideal of the
  attaching point of a rational tail has `χ = 0`.
* `Stacks.Curves.StableModel.finsum_idealPowerMultiple_ker_comp_eq_zero`: the ideal of the image
  of the complement of a rational tail has `χ = 0`.
* `Stacks.Curves.StableModel.range_inter_range_subset_singleton`: a non-contracted rational tail
  and the rest of the curve have images meeting at most in the image of the attaching point.
* `Stacks.Curves.StableModel.subsingleton_range_of_isRationalTail`: **a stable contraction maps
  every rational tail to a point**, given that the dualizing sheaves of the integral closed
  one-dimensional subschemes of the target are invertible.
* `Stacks.Curves.StableModel.exists_comp_eq_of_isIteratedContractionOfRationalTails`: a stable
  contraction factors through every chain of contractions of rational tails, through a stable
  contraction of its target.

## References

* [Stacks Project, Tag 0E7Q](https://stacks.math.columbia.edu/tag/0E7Q)
* [Stacks Project, Tag 0E34](https://stacks.math.columbia.edu/tag/0E34)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.Curves.StableModel

open Stacks.AlgebraicGeometry.PushforwardIdealSubsheaf

section Comparison

open AlgebraicGeometry.SheafOfModules.Submodule

variable {X Y : Scheme.{u}}

/-- **Over an affine open, the sections of `I 𝒪_X` are the ideal `I(U)`.** -/
theorem mem_idealPowerMultiple_unit_iff (I : X.IdealSheafData) (U : X.affineOpens)
    (f : Γ(X, U.1)) :
    f ∈ ((Stacks.Algebraization.idealPowerMultiple I 1
        (SheafOfModules.unit X.ringCatSheaf)).toSubmodule.obj (op U.1) :
          Submodule Γ(X, U.1) Γ(X, U.1)) ↔ f ∈ I.ideal U := by
  rw [Stacks.Algebraization.idealPowerMultiple_unit_toSubmodule_obj_affine, pow_one]
  exact Iff.rfl

/-- **A section lies in `I 𝒪_X` exactly when it restricts to zero on the closed subscheme cut out
by `I`**, over any open: on affine opens `I` is the kernel of restriction, and both conditions
are local. -/
theorem mem_idealPowerMultiple_unit_iff_app_eq_zero (I : X.IdealSheafData) (W : X.Opens)
    (f : Γ(X, W)) :
    f ∈ (Stacks.Algebraization.idealPowerMultiple I 1
        (SheafOfModules.unit X.ringCatSheaf)).toSubmodule.obj (op W) ↔
      I.subschemeι.app W f = 0 := by
  have hker : ∀ U : X.affineOpens, I.ideal U = RingHom.ker (I.subschemeι.app U.1).hom := by
    intro U
    rw [← Scheme.Hom.ker_apply, Scheme.IdealSheafData.ker_subschemeι]
  have hnat : ∀ (U : X.Opens) (hUW : U ≤ W),
      I.subschemeι.app U (X.presheaf.map (homOfLE hUW).op f) =
        I.subscheme.presheaf.map
          (homOfLE (show I.subschemeι ⁻¹ᵁ U ≤ I.subschemeι ⁻¹ᵁ W from
            fun _ h => hUW h)).op (I.subschemeι.app W f) := fun U hUW => by
    rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
    rfl
  constructor
  · intro hf
    refine TopCat.Presheaf.section_ext I.subscheme.sheaf _ _ 0 fun x hx => ?_
    obtain ⟨-, ⟨U, hU, rfl⟩, hxU, hUW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (show I.subschemeι x ∈ W from hx) W.isOpen
    have hres : X.presheaf.map (homOfLE hUW).op f ∈ I.ideal ⟨U, hU⟩ :=
      (mem_idealPowerMultiple_unit_iff _ ⟨U, hU⟩ _).1
        ((Stacks.Algebraization.idealPowerMultiple I 1
          (SheafOfModules.unit X.ringCatSheaf)).toSubmodule.map_mem (homOfLE hUW).op hf)
    rw [hker, RingHom.mem_ker] at hres
    have h0 := (hnat U hUW).symm.trans hres
    change I.subscheme.presheaf.germ _ x hx _ = I.subscheme.presheaf.germ _ x hx 0
    rw [map_zero, ← TopCat.Presheaf.germ_res_apply I.subscheme.presheaf
      (homOfLE (show I.subschemeι ⁻¹ᵁ U ≤ I.subschemeι ⁻¹ᵁ W from
        fun _ h => hUW h)) x hxU]
    change I.subscheme.presheaf.germ _ x hxU _ = 0
    rw [h0, map_zero]
  · intro hf
    refine mem_of_forall_affineOpens _ _ fun U hU => ?_
    change X.presheaf.map (homOfLE hU).op f ∈ ((Stacks.Algebraization.idealPowerMultiple
      I 1 (SheafOfModules.unit X.ringCatSheaf)).toSubmodule.obj
        (op U.1) : Submodule Γ(X, U.1) Γ(X, U.1))
    rw [mem_idealPowerMultiple_unit_iff, hker, RingHom.mem_ker]
    change I.subschemeι.app U.1 (X.presheaf.map (homOfLE hU).op f) = 0
    refine (hnat U.1 hU).trans ?_
    rw [hf, map_zero]

variable (I : X.IdealSheafData) (c : X ⟶ Y) [QuasiCompact (I.subschemeι ≫ c)]

/-- **Over an affine open of `Y`, a function lies in the ideal of the scheme-theoretic image of
the subscheme cut out by `I` exactly when its pullback to `X` lies in `I 𝒪_X`.** -/
theorem mem_ker_ideal_iff (V : Y.affineOpens) (s : Γ(Y, V.1))
    (t : Γ(SheafOfModules.unit X.ringCatSheaf, c ⁻¹ᵁ V.1)) (ht : t = c.app V.1 s) :
    s ∈ (I.subschemeι ≫ c).ker.ideal V ↔
      t ∈ (Stacks.Algebraization.idealPowerMultiple I 1
          (SheafOfModules.unit X.ringCatSheaf)).toSubmodule.obj (op (c ⁻¹ᵁ V.1)) := by
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
  refine Iff.trans ?_ (mem_idealPowerMultiple_unit_iff_app_eq_zero I _ t).symm
  subst ht
  exact Iff.rfl

/-- **The ideal of the scheme-theoretic image is the direct image of the ideal**: if
`𝒪_Y = c_*𝒪_X`, then under `𝒪_Y ≅ c_*𝒪_X` the subsheaf `𝓘 𝒪_Y`, for `𝓘` the ideal of the
scheme-theoretic image of the subscheme cut out by `I`, is `c_*(I 𝒪_X)`. -/
theorem exists_idealPowerMultiple_ker_iso_pushforward
    (hc : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom)) :
    ∃ e : (Stacks.Algebraization.idealPowerMultiple (I.subschemeι ≫ c).ker 1
        (SheafOfModules.unit Y.ringCatSheaf)).asModules ≅
      (Scheme.Modules.pushforward c).obj
        (Stacks.Algebraization.idealPowerMultiple I 1
          (SheafOfModules.unit X.ringCatSheaf)).asModules,
      e.hom ≫ (Scheme.Modules.pushforward c).map
          (Stacks.Algebraization.idealPowerMultiple I 1
            (SheafOfModules.unit X.ringCatSheaf)).ιModules =
        (Stacks.Algebraization.idealPowerMultiple (I.subschemeι ≫ c).ker 1
          (SheafOfModules.unit Y.ringCatSheaf)).ιModules ≫
          SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom := by
  set P := Stacks.Algebraization.idealPowerMultiple (I.subschemeι ≫ c).ker 1
    (SheafOfModules.unit Y.ringCatSheaf)
  set Q := Stacks.Algebraization.idealPowerMultiple I 1
    (SheafOfModules.unit X.ringCatSheaf)
  set N := pushforwardSubmodule c Q
  let u : SheafOfModules.unit Y.ringCatSheaf ⟶
      (Scheme.Modules.pushforward c).obj (SheafOfModules.unit X.ringCatSheaf) :=
    SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom
  have : IsIso u := hc
  have hinv : ∀ (W : Y.Opens) (t : Γ((Scheme.Modules.pushforward c).obj
      (SheafOfModules.unit X.ringCatSheaf), W)),
      c.app W ((inv u).val.app (op W) t) = t := fun W t =>
    congrArg (fun g => g.val.app (op W) t) (IsIso.inv_hom_id u)
  have h1 : ∀ (V : Y.Opensᵒᵖ) (x : P.toSheafOfModules.val.obj V),
      (P.ι ≫ u).val.app V x ∈ N.toSubmodule.obj V := by
    rintro ⟨V⟩ x
    refine mem_of_forall_affineOpens N _ fun W hW => ?_
    have hx : (P.toSheafOfModules.val.map (homOfLE hW).op x).1 ∈
        (I.subschemeι ≫ c).ker.ideal W :=
      (mem_idealPowerMultiple_unit_iff _ W _).1 (P.toSheafOfModules.val.map (homOfLE hW).op x).2
    have hnat := congrArg (fun g => g.hom x)
      ((P.ι ≫ u).val.naturality (homOfLE hW).op)
    exact (mem_ker_ideal_iff I c W _ _ hnat.symm).1 hx
  have h2 : ∀ (V : Y.Opensᵒᵖ) (x : N.toSheafOfModules.val.obj V),
      (N.ι ≫ inv u).val.app V x ∈ P.toSubmodule.obj V := by
    rintro ⟨V⟩ x
    refine mem_of_forall_affineOpens P _ fun W hW => ?_
    have hnat := congrArg (fun g => g.hom x)
      ((N.ι ≫ inv u).val.naturality (homOfLE hW).op)
    refine (mem_idealPowerMultiple_unit_iff _ W _).2 ?_
    refine (mem_ker_ideal_iff I c W _ (N.toSheafOfModules.val.map (homOfLE hW).op x).1 ?_).2
      (N.toSheafOfModules.val.map (homOfLE hW).op x).2
    exact (hinv W.1 _).symm.trans (congrArg (c.app W.1) hnat)
  let f₁ : P.toSheafOfModules ⟶ N.toSheafOfModules := N.factorThru (P.ι ≫ u) h1
  let f₂ : N.toSheafOfModules ⟶ P.toSheafOfModules := P.factorThru (N.ι ≫ inv u) h2
  have hf₁ : f₁ ≫ N.ι = P.ι ≫ u := N.factorThru_ι _ h1
  have hf₂ : f₂ ≫ P.ι = N.ι ≫ inv u := P.factorThru_ι _ h2
  let e : P.toSheafOfModules ≅ N.toSheafOfModules :=
    { hom := f₁
      inv := f₂
      hom_inv_id := by
        refine (cancel_mono P.ι).1 ?_
        refine (Category.assoc _ _ _).trans ?_
        refine (congrArg (f₁ ≫ ·) hf₂).trans ?_
        refine (Category.assoc _ _ _).symm.trans ?_
        refine (congrArg (· ≫ inv u) hf₁).trans ?_
        refine (Category.assoc _ _ _).trans ?_
        refine (congrArg (P.ι ≫ ·) (IsIso.hom_inv_id u)).trans ?_
        exact (Category.comp_id _).trans (Category.id_comp _).symm
      inv_hom_id := by
        refine (cancel_mono N.ι).1 ?_
        refine (Category.assoc _ _ _).trans ?_
        refine (congrArg (f₂ ≫ ·) hf₁).trans ?_
        refine (Category.assoc _ _ _).symm.trans ?_
        refine (congrArg (· ≫ u) hf₂).trans ?_
        refine (Category.assoc _ _ _).trans ?_
        refine (congrArg (N.ι ≫ ·) (IsIso.inv_hom_id u)).trans ?_
        exact (Category.comp_id _).trans (Category.id_comp _).symm }
  exact ⟨e, hf₁⟩

end Comparison

/-! ### Euler characteristics -/

section Euler

variable (k : Type u) [Field k]

/-- **Additivity of `χ` along a short exact sequence on a curve**, given the finite
dimensionality of the cohomology of the last two terms; that of the first follows from the long
exact sequence, and everything vanishes in degrees `≥ 2`. -/
theorem finsum_finrank_cohomologyOverField_add_of_shortExact {T : Scheme.{u}}
    (f : T ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim T ≤ 1)
    {S : ShortComplex T.Modules} (hS : S.ShortExact)
    (h₂ : ∀ n, FiniteDimensional k (cohomologyOverField k f S.X₂ n))
    (h₃ : ∀ n, FiniteDimensional k (cohomologyOverField k f S.X₃ n)) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k f S.X₂ n) : ℤ)) =
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k f S.X₁ n) : ℤ)) +
        ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k f S.X₃ n) : ℤ) := by
  obtain ⟨d, hinj, -, -, hca⟩ := exists_cohomologyOverField_longExactSequence k f hS
  have h₁ : ∀ n, FiniteDimensional k (cohomologyOverField k f S.X₁ n) := by
    intro n
    cases n with
    | zero =>
      have := h₂ 0
      exact Module.Finite.of_injective (cohomologyOverFieldMap k f S.f 0).hom hinj
    | succ m =>
      have := h₂ (m + 1)
      have := h₃ m
      exact Module.finiteDimensional_of_exact (d m).hom
        (cohomologyOverFieldMap k f S.f (m + 1)).hom (hca m)
  exact finsum_alternating_finrank_cohomologyOverField_add_of_shortExact k f hS h₁
    (fun n => finiteDimensional_cohomologyOverField_of_shortExact k f hS n (h₁ n) (h₃ n)) h₃ 2
    (isZero_cohomologyOverField_two_le k f hdim _) (isZero_cohomologyOverField_two_le k f hdim _)
    (isZero_cohomologyOverField_two_le k f hdim _)

/-- The structure sheaf of a scheme is invertible. -/
private theorem onSpace_isInvertible_unit (X : Scheme.{u}) :
    SheafOfModules.OnSpace.IsInvertible (SheafOfModules.unit X.ringCatSheaf) :=
  haveI : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (SheafOfModules.unit X.ringCatSheaf) :=
    AlgebraicGeometry.SheafOfModules.isInvertible_unit _ _
  Stacks.LocallyTrivial.onSpace_isInvertible_of_isInvertible _

/-- **`χ(M) = χ(J M) + χ(𝒪_S)`** on a curve `T`, for `M ≅ 𝒪_T` and a closed immersion `g : S ⟶ T`
with kernel `J`, by the sequence `0 ⟶ J M ⟶ M ⟶ g_* g^* M ⟶ 0`. -/
private theorem finsum_finrank_eq_add_idealPowerMultiple {T S : Scheme.{u}}
    (f : T ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim T ≤ 1) (g : S ⟶ T)
    [IsClosedImmersion g] {J : T.IdealSheafData} (hg : g.ker = J) {M : T.Modules}
    [M.IsQuasicoherent] (eM : M ≅ SheafOfModules.unit T.ringCatSheaf) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k f M n) : ℤ)) =
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k f
        (Stacks.Algebraization.idealPowerMultiple J 1 M).asModules n) : ℤ)) +
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k (g ≫ f)
        (SheafOfModules.unit S.ringCatSheaf) n) : ℤ) := by
  set N := Stacks.Algebraization.idealPowerMultiple J 1 M
  have hS := Stacks.Curves.shortExact_cokernelSequence N.ιModules
  have e₃ : cokernel N.ιModules ≅ (Scheme.Modules.pushforward g).obj
      (SheafOfModules.unit S.ringCatSheaf) :=
    Stacks.Algebraization.idealQuotientPushforwardIso J 1 M g (by rw [hg, pow_one]) ≪≫
      (Scheme.Modules.pushforward g).mapIso
        ((Scheme.Modules.pullback g).mapIso eM ≪≫ Scheme.Modules.pullbackUnitIso g)
  have hadd := finsum_finrank_cohomologyOverField_add_of_shortExact k f hdim hS
    (fun n => have := forall_finiteDimensional_cohomologyOverField_unit k f n
      Module.Finite.equiv (cohomologyOverFieldIso k f eM n).toLinearEquiv.symm)
    (fun n => have := forall_finiteDimensional_cohomologyOverField_unit k (g ≫ f) n
      Module.Finite.equiv ((cohomologyOverFieldIso k f e₃ n) ≪≫
        (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k g f _ n).symm).toLinearEquiv.symm)
  have e3 := finsum_congr fun n => congrArg (fun m : ℕ => (-1 : ℤ) ^ n * (m : ℤ))
    ((finrank_cohomologyOverField_eq_of_iso k f e₃ n).trans
      (finrank_cohomologyOverField_pushforward_of_isClosedImmersion k g f _ n).symm)
  change (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k f M n) : ℤ)) =
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k f N.asModules n) : ℤ)) +
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k
        (cohomologyOverField k f (cokernel N.ιModules) n) : ℤ) at hadd
  rwa [e3] at hadd

/-- **The ideal of the attaching point of a rational tail has Euler characteristic zero.** Let
`C` be a rational tail of `X` with attaching point cut out by `K = C ⊔ 𝓙` and let `𝓘'` be the ideal
of `C ∩ X'` in `C`. Then `χ(C, 𝓘' 𝒪_C) = χ(C, 𝒪_C) - χ(C ∩ X', 𝒪) = [k' : k] - [k' : k] = 0`. -/
theorem finsum_idealPowerMultiple_ker_inclusion_eq_zero {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hdim : topologicalKrullDim X = 1) {C : X.IdealSheafData} (hC : IsRationalTail k X C) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k
      (C.subschemeι ≫ (X ↘ Spec (.of k)))
      (Stacks.Algebraization.idealPowerMultiple (Scheme.IdealSheafData.inclusion
        (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C)).ker 1
        ((Scheme.Modules.pullback C.subschemeι).obj
          (SheafOfModules.unit X.ringCatSheaf))).asModules n) : ℤ)) = 0 := by
  set fC := C.subschemeι ≫ (X ↘ Spec (.of k))
  set K := intersectionWithComplementaryCurveIdeal C
  set incl := Scheme.IdealSheafData.inclusion (le_sup_left : C ≤ K)
  set M := (Scheme.Modules.pullback C.subschemeι).obj (SheafOfModules.unit X.ringCatSheaf)
  have hCdim : topologicalKrullDim C.subscheme ≤ 1 :=
    le_of_eq (Stacks.Curves.topologicalKrullDim_subscheme_eq_one_of_isRationalTail k X hdim C hC)
  have eM : M ≅ SheafOfModules.unit C.subscheme.ringCatSheaf :=
    Scheme.Modules.pullbackUnitIso C.subschemeι
  have : M.IsQuasicoherent := Stacks.Modules.isQuasicoherent_pullback _ _
    (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X)
  have hinclf : incl ≫ fC = K.subschemeι ≫ (X ↘ Spec (.of k)) := by
    simp only [fC, incl, ← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
    rfl
  have h₂ : ∀ n, Module.finrank k (cohomologyOverField k fC M n) =
      Module.finrank k
        (cohomologyOverField k fC (SheafOfModules.unit C.subscheme.ringCatSheaf) n) :=
    fun n => finrank_cohomologyOverField_eq_of_iso k fC eM n
  have hadd := finsum_finrank_eq_add_idealPowerMultiple k fC hCdim incl rfl eM
  have hO := eulerCharacteristic_unit_of_isRationalTail hdim hC
  unfold eulerCharacteristic at hO
  have hI := finrank_globalSections_intersection_of_isRationalTail hC
  have : IsIso (Scheme.IdealSheafData.inclusion
      (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C) ≫ C.subscheme.toSpecΓ) :=
    isIso_inclusion_comp_toSpecΓ_of_isRationalTail hC
  have : IsAffine K.subscheme := IsAffine.of_isIso (incl ≫ C.subscheme.toSpecΓ)
  have hP := finsum_alternating_finrank_unit_eq_finrank_of_isAffine (incl ≫ fC)
  rw [hinclf] at hP hadd
  simp only [h₂] at hadd
  rw [hO, hP, hI] at hadd
  linarith

/-- **The ideal of the image of the complement of a rational tail has Euler characteristic zero.**
Let `C` be a rational tail of a nodal curve `X`, `X'` the closure of its complement, and
`c : X ⟶ Y` with `𝒪_Y = c_*𝒪_X`, with `Y` proper over `k` and `c|_C` affine. Then the ideal `𝓘` of
the scheme-theoretic image of `X'` satisfies `χ(Y, 𝓘) = 0`: by
`Stacks.Curves.StableModel.exists_idealPowerMultiple_ker_iso_pushforward` it is `c_*(𝓙 𝒪_X)`, which
is `(c|_C)_*(𝓘' 𝒪_C)` for `𝓘'` the ideal of `C ∩ X'` in `C`
(`Stacks.Curves.nonempty_pushforward_idealPowerMultiple_ker_iso`), and `c|_C` is affine. -/
theorem finsum_idealPowerMultiple_ker_comp_eq_zero {X Y : Scheme.{u}} [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hdim : topologicalKrullDim X = 1) (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalTail k X C) (gY : Y ⟶ Spec (.of k)) [IsProper gY]
    (c : X ⟶ Y) (hcg : c ≫ gY = X ↘ Spec (.of k)) [IsAffineHom (C.subschemeι ≫ c)]
    [QuasiCompact ((complementaryCurveIdeal C).subschemeι ≫ c)]
    (hcO : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom)) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k gY
      (Stacks.Algebraization.idealPowerMultiple
        ((complementaryCurveIdeal C).subschemeι ≫ c).ker 1
        (SheafOfModules.unit Y.ringCatSheaf)).asModules n) : ℤ)) = 0 := by
  have : IsReduced X := Stacks.Curves.isReduced_of_hasAtWorstNodalSingularities k X hnodal
  have := onSpace_isInvertible_unit X
  have := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
  set K := intersectionWithComplementaryCurveIdeal C
  set incl := Scheme.IdealSheafData.inclusion (le_sup_left : C ≤ K)
  set M := (Scheme.Modules.pullback C.subschemeι).obj (SheafOfModules.unit X.ringCatSheaf)
  have : M.IsQuasicoherent := Stacks.Modules.isQuasicoherent_pullback _ _
    (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X)
  set N := Stacks.Algebraization.idealPowerMultiple incl.ker 1 M
  have : N.asModules.IsQuasicoherent := by
    have h := Stacks.AlgebraicGeometry.IdealPowerComparison.isQuasicoherent_idealPowerMultiple
      incl.ker 1 M
    rwa [← Stacks.AlgebraicGeometry.IdealPowerComparison.algebraization_idealPowerMultiple_eq]
      at h
  obtain ⟨e₁, -⟩ := exists_idealPowerMultiple_ker_iso_pushforward (complementaryCurveIdeal C) c hcO
  obtain ⟨e₂⟩ := Stacks.Curves.nonempty_pushforward_idealPowerMultiple_ker_iso
    (SheafOfModules.unit X.ringCatSheaf) C K
    (Stacks.Curves.tail_inf_complementaryCurveIdeal_eq_bot k X hdim hnodal C hC) rfl le_sup_left
  let e : (Stacks.Algebraization.idealPowerMultiple
        ((complementaryCurveIdeal C).subschemeι ≫ c).ker 1
        (SheafOfModules.unit Y.ringCatSheaf)).asModules ≅
      (Scheme.Modules.pushforward (C.subschemeι ≫ c)).obj N.asModules :=
    e₁ ≪≫ (Scheme.Modules.pushforward c).mapIso e₂.symm ≪≫
      (Scheme.Modules.pushforwardComp C.subschemeι c).app _
  have hfC : (C.subschemeι ≫ c) ≫ gY = C.subschemeι ≫ (X ↘ Spec (.of k)) := by
    rw [Category.assoc, hcg]
  have h := finsum_idealPowerMultiple_ker_inclusion_eq_zero k hdim hC
  rw [← h]
  refine finsum_congr fun n => ?_
  rw [finrank_cohomologyOverField_eq_of_iso k gY e n,
    ← finrank_cohomologyOverField_pushforward_of_isAffineHom k (C.subschemeι ≫ c) gY, hfC]

/-- The cohomology of `i_* i^* 𝒪_Y` along a closed immersion `i` is that of `𝒪` on the source. -/
theorem finrank_cohomologyOverField_pushforward_pullback_unit {T Y : Scheme.{u}}
    (gY : Y ⟶ Spec (.of k)) (i : T ⟶ Y) [IsClosedImmersion i] (n : ℕ) :
    Module.finrank k (cohomologyOverField k gY ((Scheme.Modules.pushforward i).obj
      ((Scheme.Modules.pullback i).obj (SheafOfModules.unit Y.ringCatSheaf))) n) =
      Module.finrank k (cohomologyOverField k (i ≫ gY)
        (SheafOfModules.unit T.ringCatSheaf) n) := by
  rw [← finrank_cohomologyOverField_pushforward_of_isClosedImmersion k i gY]
  exact finrank_cohomologyOverField_eq_of_iso k _ (Scheme.Modules.pullbackUnitIso i) n

/-- Finite dimensionality of the cohomology of `i_* i^* 𝒪_Y` along a closed immersion. -/
theorem finiteDimensional_cohomologyOverField_pushforward_pullback_unit {T Y : Scheme.{u}}
    (gY : Y ⟶ Spec (.of k)) [IsProper gY] (i : T ⟶ Y) [IsClosedImmersion i] (n : ℕ) :
    FiniteDimensional k (cohomologyOverField k gY ((Scheme.Modules.pushforward i).obj
      ((Scheme.Modules.pullback i).obj (SheafOfModules.unit Y.ringCatSheaf))) n) := by
  have := forall_finiteDimensional_cohomologyOverField_unit k (i ≫ gY) n
  have e : (Scheme.Modules.pullback i).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit T.ringCatSheaf := Scheme.Modules.pullbackUnitIso i
  exact Module.Finite.equiv ((cohomologyOverFieldIso k (i ≫ gY) e.symm n) ≪≫
      cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k i gY _ n).toLinearEquiv

/-- **`χ` along the union of two closed subschemes**: if `I ⊓ J = ⊥` on a curve `Y`, then
`χ(𝒪_Y) + χ(𝒪_{I ⊔ J}) = χ(𝒪_I) + χ(𝒪_J)`, by the sequence
`0 ⟶ 𝒪_Y ⟶ 𝒪_I ⊕ 𝒪_J ⟶ 𝒪_{I ⊔ J} ⟶ 0`. -/
theorem finsum_finrank_unit_add_of_inf_eq_bot {Y : Scheme.{u}} (gY : Y ⟶ Spec (.of k))
    [IsProper gY] (hdim : topologicalKrullDim Y ≤ 1) {I J : Y.IdealSheafData}
    (hbot : I ⊓ J = ⊥) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k gY
        (SheafOfModules.unit Y.ringCatSheaf) n) : ℤ)) +
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k
        ((I ⊔ J).subschemeι ≫ gY) (SheafOfModules.unit (I ⊔ J).subscheme.ringCatSheaf) n) : ℤ)) =
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k
        (I.subschemeι ≫ gY) (SheafOfModules.unit I.subscheme.ringCatSheaf) n) : ℤ)) +
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k
        (J.subschemeι ≫ gY) (SheafOfModules.unit J.subscheme.ringCatSheaf) n) : ℤ) := by
  have := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit Y
  have := onSpace_isInvertible_unit Y
  obtain ⟨a, b, w, hS⟩ :=
    Stacks.Curves.exists_shortExact_restrictions (SheafOfModules.unit Y.ringCatSheaf) hbot rfl
  have hfin := fun (T : Scheme.{u}) (i : T ⟶ Y) (_ : IsClosedImmersion i) n =>
    finiteDimensional_cohomologyOverField_pushforward_pullback_unit k gY i n
  have hadd := finsum_finrank_cohomologyOverField_add_of_shortExact k gY hdim hS
    (fun n => finiteDimensional_cohomologyOverField_biprod k gY _ _ n
      (hfin _ I.subschemeι inferInstance n) (hfin _ J.subschemeι inferInstance n))
    (fun n => hfin _ (I ⊔ J).subschemeι inferInstance n)
  have hbi : ∀ n, Module.finrank k (cohomologyOverField k gY (ShortComplex.mk a b w).X₂ n) =
      Module.finrank k (cohomologyOverField k (I.subschemeι ≫ gY)
        (SheafOfModules.unit I.subscheme.ringCatSheaf) n) +
      Module.finrank k (cohomologyOverField k (J.subschemeι ≫ gY)
        (SheafOfModules.unit J.subscheme.ringCatSheaf) n) := fun n => by
    obtain ⟨e⟩ := nonempty_cohomologyOverField_biprod_linearEquiv k gY
      ((Scheme.Modules.pushforward I.subschemeι).obj
        ((Scheme.Modules.pullback I.subschemeι).obj (SheafOfModules.unit Y.ringCatSheaf)))
      ((Scheme.Modules.pushforward J.subschemeι).obj
        ((Scheme.Modules.pullback J.subschemeι).obj (SheafOfModules.unit Y.ringCatSheaf))) n
    have := hfin _ I.subschemeι inferInstance n
    have := hfin _ J.subschemeι inferInstance n
    rw [← finrank_cohomologyOverField_pushforward_pullback_unit k gY I.subschemeι,
      ← finrank_cohomologyOverField_pushforward_pullback_unit k gY J.subschemeι,
      ← Module.finrank_prod]
    exact e.finrank_eq
  have h₃ : ∀ n, Module.finrank k (cohomologyOverField k gY (ShortComplex.mk a b w).X₃ n) =
      Module.finrank k (cohomologyOverField k ((I ⊔ J).subschemeι ≫ gY)
        (SheafOfModules.unit (I ⊔ J).subscheme.ringCatSheaf) n) := fun n =>
    finrank_cohomologyOverField_pushforward_pullback_unit k gY _ n
  have e2 := finsum_congr fun n => congrArg (fun m : ℕ => (-1 : ℤ) ^ n * (m : ℤ)) (hbi n)
  have e3 := finsum_congr fun n => congrArg (fun m : ℕ => (-1 : ℤ) ^ n * (m : ℤ)) (h₃ n)
  simp only [Nat.cast_add, mul_add] at e2
  have hsupp : ∀ (T : Scheme.{u}) (i : T ⟶ Y) [IsClosedImmersion i],
      (Function.support fun n : ℕ => (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k
        (i ≫ gY) (SheafOfModules.unit T.ringCatSheaf) n) : ℤ)).Finite := by
    intro T i _
    refine (Set.finite_lt_nat 2).subset fun n hn => ?_
    by_contra h2
    refine hn ?_
    have hT : topologicalKrullDim T ≤ 1 :=
      (i.isClosedEmbedding.isInducing.topologicalKrullDim_le).trans hdim
    have hz := isZero_cohomologyOverField_two_le k (i ≫ gY) hT
      (SheafOfModules.unit T.ringCatSheaf) n (by simp only [Set.mem_ofPred_eq, not_lt] at h2; omega)
    have := ModuleCat.subsingleton_of_isZero hz
    simp [Module.finrank_zero_of_subsingleton]
  rw [e2, e3, finsum_add_distrib (hsupp _ I.subschemeι) (hsupp _ J.subschemeι)] at hadd
  change _ + _ = _ + _ at hadd
  linarith

/-- **`χ(𝒪_Y) = χ(I 𝒪_Y) + χ(𝒪_I)`** on a curve, by the sequence `0 ⟶ I 𝒪_Y ⟶ 𝒪_Y ⟶ 𝒪_I ⟶ 0`. -/
theorem finsum_finrank_unit_eq_add_idealPowerMultiple {Y : Scheme.{u}} (gY : Y ⟶ Spec (.of k))
    [IsProper gY] (hdim : topologicalKrullDim Y ≤ 1) (I : Y.IdealSheafData) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k gY
        (SheafOfModules.unit Y.ringCatSheaf) n) : ℤ)) =
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k gY
        (Stacks.Algebraization.idealPowerMultiple I 1
          (SheafOfModules.unit Y.ringCatSheaf)).asModules n) : ℤ)) +
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k
        (I.subschemeι ≫ gY) (SheafOfModules.unit I.subscheme.ringCatSheaf) n) : ℤ) := by
  have : (SheafOfModules.unit Y.ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _
  exact finsum_finrank_eq_add_idealPowerMultiple k gY hdim I.subschemeι
    (Scheme.IdealSheafData.ker_subschemeι I) (Iso.refl _)

/-- **`χ` of the structure sheaf is monotone on zero-dimensional closed subschemes**: if the
subscheme cut out by `J` lies in the zero-dimensional one cut out by `I ≤ J`, then
`χ(𝒪_J) ≤ χ(𝒪_I)`, the difference being `h⁰` of the ideal of the first in the second. -/
theorem finsum_finrank_unit_le_of_le {Y : Scheme.{u}} (gY : Y ⟶ Spec (.of k)) [IsProper gY]
    {I J : Y.IdealSheafData} (hIJ : I ≤ J) (hI : topologicalKrullDim I.subscheme ≤ 0) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k (J.subschemeι ≫ gY)
        (SheafOfModules.unit J.subscheme.ringCatSheaf) n) : ℤ)) ≤
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k (I.subschemeι ≫ gY)
        (SheafOfModules.unit I.subscheme.ringCatSheaf) n) : ℤ) := by
  set fI := I.subschemeι ≫ gY
  set incl := Scheme.IdealSheafData.inclusion hIJ
  set M : I.subscheme.Modules := SheafOfModules.unit I.subscheme.ringCatSheaf
  have : M.IsQuasicoherent := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _
  have hinclf : incl ≫ fI = J.subschemeι ≫ gY := by
    simp only [fI, incl, ← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  have hadd := finsum_finrank_eq_add_idealPowerMultiple k fI
    (hI.trans (by exact_mod_cast zero_le_one)) incl rfl (Iso.refl M)
  have hN := finsum_alternating_finrank_cohomologyOverField_eq_finrank_zero k fI
    (Stacks.Algebraization.idealPowerMultiple incl.ker 1 M).asModules
    fun i hi => isZero_cohomologyOverField_of_topologicalKrullDim_le k fI _ (d := 0)
      (by exact_mod_cast hI) hi
  rw [hinclf, hN] at hadd
  omega

end Euler
/-- A scheme with a locally finite type, quasi-compact morphism to `Spec k` is noetherian. -/
private theorem isNoetherian_of_hom_to_spec {k : Type u} [Field k] {T : Scheme.{u}}
    (f : T ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] : IsNoetherian T :=
  haveI := LocallyOfFiniteType.isLocallyNoetherian f
  haveI := QuasiCompact.compactSpace_of_compactSpace f
  ⟨⟩

/-! ### The images of a non-contracted rational tail and of the rest of the curve -/

section Topology

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))]

/-- A closed subscheme and the closure of its complement cover the scheme. -/
theorem support_union_support_complementaryCurveIdeal (C : X.IdealSheafData) :
    (C.support : Set X) ∪ (complementaryCurveIdeal C).support = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  by_cases hx : x ∈ (C.support : Set X)
  · exact Or.inl hx
  · refine Or.inr (Scheme.Hom.range_subset_ker_support (Scheme.Opens.ι C.support.compl) ?_)
    rw [Scheme.Opens.range_ι]
    exact hx

/-- **A non-contracted rational tail and the rest of the curve meet only over the attaching
point.** Let `c : X ⟶ Y` be proper with `𝒪_Y = c_*𝒪_X` and let `C` be a rational tail of `X`,
attached at `x`, which `c` does not map to a point. A point of `C ∖ X'` is alone in its fibre,
the fibres of `c` being connected and those of `c|_C` discrete; so a point in the images of both
`C` and `X'` is the image of a point of `C ∩ X' = {x}`. -/
theorem range_inter_range_subset_singleton [IsProper (X ↘ Spec (.of k))] {C : X.IdealSheafData}
    (hC : IsRationalTail k X C) (c : X ⟶ Y) [IsProper c]
    (hiso : ∀ U : Y.Opens, IsIso (c.app U)) (hCdim : topologicalKrullDim C.subscheme ≤ 1)
    (hns : ¬ (Set.range (C.subschemeι ≫ c)).Subsingleton) :
    Set.range (C.subschemeι ≫ c) ∩ Set.range ((complementaryCurveIdeal C).subschemeι ≫ c) ⊆
      {c (C.subschemeι hC.attachingPoint)} := by
  have : IsIntegral C.subscheme := hC.isIntegral
  have : IsNoetherian C.subscheme :=
    isNoetherian_of_hom_to_spec (C.subschemeι ≫ (X ↘ Spec (.of k)))
  rintro y ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
  set a' := C.subschemeι a
  set b' := (complementaryCurveIdeal C).subschemeι b
  have ha'C : a' ∈ (C.support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨a, rfl⟩
  have hb'X : b' ∈ ((complementaryCurveIdeal C).support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨b, rfl⟩
  have hfib : c b' = c a' := hb
  by_cases ha'X : a' ∈ ((complementaryCurveIdeal C).support : Set X)
  · have hmem : a' ∈ ((intersectionWithComplementaryCurveIdeal C).support : Set X) := by
      rw [Scheme.IdealSheafData.support_sup]
      exact ⟨ha'C, ha'X⟩
    rw [hC.intersectionWithComplementaryCurveIdeal_eq,
      Scheme.IdealSheafData.coe_support_vanishingIdeal] at hmem
    change c a' = _
    rw [Set.mem_singleton_iff.mp hmem]
  · exfalso
    have hdisc := AlgebraicGeometry.isDiscrete_preimage_singleton_of_not_subsingleton_range hCdim
      (C.subschemeι ≫ c).continuous (C.subschemeι ≫ c).isClosedMap hns ((C.subschemeι ≫ c) a)
    have himg : (C.support : Set X) ∩ c ⁻¹' {c a'} =
        C.subschemeι '' ((C.subschemeι ≫ c) ⁻¹' {(C.subschemeι ≫ c) a}) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      ext z
      constructor
      · rintro ⟨⟨w, rfl⟩, hzc⟩
        exact ⟨w, hzc, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨⟨w, rfl⟩, hw⟩
    have hdisc' : IsDiscrete ((C.support : Set X) ∩ c ⁻¹' {c a'}) := by
      rw [himg]
      exact hdisc.image C.subschemeι.isClosedEmbedding.isInducing
    have hconn := (c.isConnected_preimage_singleton_of_isIso_app hiso (c a')).isPreconnected
    have hsing := _root_.preimage_singleton_eq_singleton_of_mem_diff C.support.isClosed
      (complementaryCurveIdeal C).support.isClosed
      (support_union_support_complementaryCurveIdeal C) ha'C ha'X hconn hdisc'
    have : b' ∈ c ⁻¹' {c a'} := hfib
    rw [hsing, Set.mem_singleton_iff] at this
    exact ha'X (this ▸ hb'X)

end Topology

/-! ### A stable contraction contracts every rational tail -/

section Main

variable (k : Type u) [Field k]

/-- A subsingleton space has dimension at most zero. -/
theorem topologicalKrullDim_le_zero_of_subsingleton (T : Type*) [TopologicalSpace T]
    [Subsingleton T] : topologicalKrullDim T ≤ 0 := by
  refine Order.krullDim_nonpos_iff_forall_isMax.mpr fun S T' hST => ?_
  obtain ⟨x, hx⟩ := S.isIrreducible.nonempty
  intro y _
  exact (Subsingleton.elim x y ▸ hx : y ∈ (S : Set T))

/-- An irreducible quasi-sober `T₀` space with two distinct points has dimension at least one:
some point is not generic, and its closure is strictly smaller than the whole space. -/
theorem one_le_topologicalKrullDim_of_not_subsingleton (T : Type*) [TopologicalSpace T]
    [IrreducibleSpace T] [QuasiSober T] [T0Space T] (h : ¬ Subsingleton T) :
    1 ≤ topologicalKrullDim T := by
  obtain ⟨p, hp⟩ : ∃ p : T, closure ({p} : Set T) ≠ Set.univ := by
    by_contra hcon
    push Not at hcon
    exact h ⟨fun a b => ((isGenericPoint_def.mpr (hcon a)).eq
      (isGenericPoint_def.mpr (hcon b)))⟩
  refine Order.one_le_krullDim_iff.mpr ⟨⟨closure {p}, isIrreducible_singleton.closure,
    isClosed_closure⟩, ⟨Set.univ, IrreducibleSpace.isIrreducible_univ T, isClosed_univ⟩, ?_⟩
  exact lt_of_le_of_ne (fun _ _ => Set.mem_univ _) fun he => hp (congrArg (fun S => S.1) he)

/-- A proper scheme over `k` of dimension at most zero has nonnegative Euler characteristic. -/
private theorem finsum_finrank_nonneg_of_topologicalKrullDim_le_zero {T : Scheme.{u}}
    (f : T ⟶ Spec (.of k)) [IsProper f] (F : T.Modules) (hdim : topologicalKrullDim T ≤ 0) :
    0 ≤ ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k f F n) : ℤ) := by
  rw [finsum_alternating_finrank_cohomologyOverField_eq_finrank_zero k f F
    fun i hi => isZero_cohomologyOverField_of_topologicalKrullDim_le k f F (d := 0)
      (by exact_mod_cast hdim) hi]
  positivity

/-- If `H⁰(Y, 𝒪_Y) ⟶ H⁰(X, 𝒪_X)` is an isomorphism and `X` has global sections `k` through
`c ≫ g`, then `Y` has global sections `k` through `g`. -/
private theorem isIso_globalSections_of_isIso_comp {X Y : Scheme.{u}} (c : X ⟶ Y)
    (g : Y ⟶ Spec (.of k)) [IsIso c.appTop]
    (h : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (c ≫ g).appTop)) :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop) := by
  rw [Scheme.Hom.comp_appTop, ← Category.assoc] at h
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ c.appTop _ h

/-- **A stable contraction maps every rational tail to a point.** Let `X` be a proper nodal curve
over `k` with `H⁰(X, 𝒪_X) = k`, `C` a rational tail of `X` and `c : X ⟶ Y` a morphism satisfying
the conditions of [Stacks, Tag 0E7Q], and suppose `ω_D` is invertible over `Γ(D, 𝒪_D)` for every
one-dimensional integral closed subscheme `D` of `Y`. Then `c(C)` is a point.

Otherwise `c|_C` is finite onto an integral curve `D ⊆ Y`. Let `Z` be the scheme-theoretic image
of the closure `X'` of the complement of `C`. Its ideal has `χ = 0`
(`Stacks.Curves.StableModel.finsum_idealPowerMultiple_ker_comp_eq_zero`), so
`χ(𝒪_Y) = χ(𝒪_Z)`; as `D ∪ Z = Y`, `χ(𝒪_D) = χ(𝒪_{D ∩ Z}) ≥ χ(𝒪_{D ∩ Y'})`, where `Y'` is the
closure of `Y ∖ D` and `D ∩ Z` is at most a point. By [Stacks, Tag 0E34] the degree of `ω_Y` on
`D` is `χ(𝒪_{D ∩ Y'}) - 2 χ(𝒪_D) ≤ 0`, while ampleness of `ω_Y` makes it positive. -/
theorem subsingleton_range_of_isRationalTail {X Y : Scheme.{u}} [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hdim : topologicalKrullDim X = 1) (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalTail k X C) {gY : Y ⟶ Spec (.of k)} {c : X ⟶ Y}
    (hst : IsStableContraction (X ↘ Spec (.of k)) gY c)
    (hωY : ∀ (D : Y.IdealSheafData) (_ : IsIntegral D.subscheme)
      (_ : topologicalKrullDim D.subscheme = 1),
      haveI : IsProper gY := hst.isProper
      letI : Field Γ(D.subscheme, ⊤) :=
        (isField_of_universallyClosed k (D.subschemeι ≫ gY)).toField
      haveI : IsProper D.subscheme.toSpecΓ :=
        Stacks.AlgebraicGeometry.ProperGeomConnected.isProper_toSpecΓ (D.subschemeι ≫ gY)
      SheafOfModules.IsInvertible D.subscheme.presheaf D.subscheme.ringCatSheaf.2
        (Stacks.Duality.dualizingSheafOverField D.subscheme.toSpecΓ)) :
    (Set.range (C.subschemeι ≫ c)).Subsingleton := by
  by_contra hns
  have : IsProper gY := hst.isProper
  have : IsProper (c ≫ gY) := hst.comp_eq ▸ inferInstance
  have : IsProper c := IsProper.of_comp c gY
  have hiso : ∀ U : Y.Opens, IsIso (c.app U) :=
    Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit c
      hst.isIso_unitToPushforwardObjUnit
  have : Surjective c := c.surjective_of_isIso_app hiso
  have : IsIntegral C.subscheme := hC.isIntegral
  have hCdim := Stacks.Curves.topologicalKrullDim_subscheme_eq_one_of_isRationalTail k X hdim C hC
  have : IsNoetherian C.subscheme :=
    isNoetherian_of_hom_to_spec (C.subschemeι ≫ (X ↘ Spec (.of k)))
  set h := C.subschemeι ≫ c
  have : IsFinite h := h.isFinite_of_not_subsingleton_range hCdim.le hns
  have : IsReduced Y := hst.isReduced
  have hYdim : topologicalKrullDim Y = 1 := hst.topologicalKrullDim_eq
  have : IsNoetherian Y := isNoetherian_of_hom_to_spec gY
  set Z := ((complementaryCurveIdeal C).subschemeι ≫ c).ker
  set D := h.ker
  -- `χ(𝒪_Y) = χ(𝒪_Z)`
  have hP := finsum_idealPowerMultiple_ker_comp_eq_zero k hdim hnodal hC gY c hst.comp_eq
    hst.isIso_unitToPushforwardObjUnit
  have hYZ := finsum_finrank_unit_eq_add_idealPowerMultiple k gY hYdim.le Z
  -- the supports of `D` and `Z` are the images of `C` and `X'`, and cover `Y`
  have hsuppD : (D.support : Set Y) = Set.range h := by
    rw [Scheme.Hom.support_ker]
    exact h.isClosedMap.isClosed_range.closure_eq
  have hsuppZ : (Z.support : Set Y) = Set.range ((complementaryCurveIdeal C).subschemeι ≫ c) := by
    rw [Scheme.Hom.support_ker]
    exact (Scheme.Hom.isClosedMap _).isClosed_range.closure_eq
  have hcov : ∀ y : Y, y ∈ (D.support : Set Y) ∨ y ∈ (Z.support : Set Y) := fun y => by
    obtain ⟨p, rfl⟩ := c.surjective y
    rcases (support_union_support_complementaryCurveIdeal C ▸ Set.mem_univ p :
      p ∈ (C.support : Set X) ∪ (complementaryCurveIdeal C).support) with hp | hp
    · rw [← Scheme.IdealSheafData.range_subschemeι] at hp
      obtain ⟨q, rfl⟩ := hp
      exact Or.inl (hsuppD ▸ ⟨q, rfl⟩)
    · rw [← Scheme.IdealSheafData.range_subschemeι] at hp
      obtain ⟨q, rfl⟩ := hp
      exact Or.inr (hsuppZ ▸ ⟨q, rfl⟩)
  have hDZ : D ⊓ Z = ⊥ := by
    rw [← Scheme.IdealSheafData.support_eq_top_iff]
    refine le_antisymm le_top fun y _ => ?_
    rcases hcov y with hy | hy
    · exact Scheme.IdealSheafData.support_antitone inf_le_left hy
    · exact Scheme.IdealSheafData.support_antitone inf_le_right hy
  -- `Y' ⊆ Z`
  have hZY' : Z ≤ complementaryCurveIdeal D := by
    change Z ≤ (Scheme.Opens.ι D.support.compl).ker
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range,
      ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    refine closure_minimal (fun y hy => ?_) Z.support.isClosed
    rw [Scheme.Opens.range_ι] at hy
    exact (hcov y).resolve_left hy
  -- `D ∩ Z` is at most a point
  have hint := range_inter_range_subset_singleton hC c hiso hCdim.le hns
  have hsub : Subsingleton (D ⊔ Z).subscheme := by
    refine ⟨fun a b => (D ⊔ Z).subschemeι.isClosedEmbedding.injective ?_⟩
    have hmem : ∀ w : (D ⊔ Z).subscheme,
        (D ⊔ Z).subschemeι w = c (C.subschemeι hC.attachingPoint) :=
      fun w => by
        have hw : (D ⊔ Z).subschemeι w ∈ ((D ⊔ Z).support : Set Y) := by
          rw [← Scheme.IdealSheafData.range_subschemeι]
          exact ⟨w, rfl⟩
        rw [Scheme.IdealSheafData.support_sup] at hw
        exact hint ⟨hsuppD ▸ hw.1, hsuppZ ▸ hw.2⟩
    rw [hmem a, hmem b]
  have hdimDZ := topologicalKrullDim_le_zero_of_subsingleton (D ⊔ Z).subscheme
  have hdimDY := topologicalKrullDim_intersectionWithComplementaryCurve_le_zero
    hYdim.le D
  have hun := finsum_finrank_unit_add_of_inf_eq_bot k gY hYdim.le hDZ
  have hle := finsum_finrank_unit_le_of_le k gY (sup_le_sup_left hZY' D) hdimDZ
  have hδ := finsum_finrank_nonneg_of_topologicalKrullDim_le_zero k
    ((D ⊔ complementaryCurveIdeal D).subschemeι ≫ gY)
    (SheafOfModules.unit (D ⊔ complementaryCurveIdeal D).subscheme.ringCatSheaf) hdimDY
  -- `D` is an integral curve
  have : IsReduced D.subscheme := Scheme.Hom.isReduced_image h
  have : IrreducibleSpace D.subscheme := Scheme.IdealSheafData.irreducibleSpace_subscheme Y D (by
    rw [Scheme.IdealSheafData.range_subschemeι, hsuppD, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ C.subscheme).image h h.continuous.continuousOn)
  have : IsIntegral D.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have hDdim : topologicalKrullDim D.subscheme = 1 := by
    refine le_antisymm (D.subschemeι.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans
      hYdim.le) (one_le_topologicalKrullDim_of_not_subsingleton _ fun hsub => hns ?_)
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    obtain ⟨a', ha'⟩ : h a ∈ Set.range D.subschemeι := by
      rw [Scheme.IdealSheafData.range_subschemeι, hsuppD]
      exact ⟨a, rfl⟩
    obtain ⟨b', hb'⟩ : h b ∈ Set.range D.subschemeι := by
      rw [Scheme.IdealSheafData.range_subschemeι, hsuppD]
      exact ⟨b, rfl⟩
    rw [← ha', ← hb', Subsingleton.elim a' b']
  -- the sequence `0 ⟶ ω_D ⟶ ω_Y|_D ⟶ 𝒪_{D ∩ Y'} ⟶ 0` of [Stacks, Tag 0E34]
  obtain ⟨hωinv, hL⟩ := hst.isAmple
  let : Y.Over (Spec (.of k)) := ⟨gY⟩
  have : IsProper (Y ↘ Spec (.of k)) := hst.isProper
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (Y ↘ Spec (.of k)).appTop) := by
    have : IsIso c.appTop := hiso ⊤
    refine isIso_globalSections_of_isIso_comp k c gY ?_
    rw [hst.comp_eq]
    infer_instance
  have hYeq : TopologicalSpace.Equidimensional Y :=
    equidimensional_of_isIso_globalSections_of_dimension_one k (Y ↘ Spec (.of k)) hYdim
  have hDeq : TopologicalSpace.Equidimensional D.subscheme :=
    TopologicalSpace.Equidimensional.of_preirreducibleSpace D.subscheme
  obtain ⟨a, b, w, hS⟩ := (Stacks.Curves.dualizingSheafOverField_closedSubcurve_of_isInvertible
    gY hYeq hYdim D hDeq hDdim).2.2.2.2.2.2.2.2.1
  set fD := D.subschemeι ≫ gY
  let : SheafOfModules.IsInvertible D.subscheme.presheaf D.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback D.subschemeι).obj (Stacks.Duality.dualizingSheafOverField gY)) :=
    Stacks.Modules.isInvertible_pullback D.subschemeι _
  let : Field Γ(D.subscheme, ⊤) := (isField_of_universallyClosed k fD).toField
  let : Algebra k Γ(D.subscheme, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ fD.appTop).hom.toAlgebra
  have : IsProper D.subscheme.toSpecΓ :=
    Stacks.AlgebraicGeometry.ProperGeomConnected.isProper_toSpecΓ fD
  have := hωY D inferInstance hDdim
  have : IsIso ((Scheme.ΓSpecIso (.of Γ(D.subscheme, ⊤))).inv ≫
      D.subscheme.toSpecΓ.appTop) := by
    rw [Scheme.toSpecΓ_appTop]
    infer_instance
  have hf : D.subscheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap k Γ(D.subscheme, ⊤))) =
      D.subschemeι ≫ (Y ↘ Spec (.of k)) := by
    change D.subscheme.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ fD.appTop) = fD
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
    simp
  have hdeg := invertibleCurveDegree_eq_sub_two_mul_of_shortExact D hDdim.le
    Γ(D.subscheme, ⊤) D.subscheme.toSpecΓ hf hS (Iso.refl _) (Iso.refl _)
  have hpos := invertibleCurveDegree_pullback_pos_of_isAmple_of_isAffineHom k fD hDdim
    D.subschemeι _ hL
  change 0 < invertibleCurveDegree k fD hDdim.le
    ((Scheme.Modules.pullback D.subschemeι).obj (Stacks.Duality.dualizingSheafOverField gY)) at hpos
  change invertibleCurveDegree k fD hDdim.le
    ((Scheme.Modules.pullback D.subschemeι).obj (Stacks.Duality.dualizingSheafOverField gY)) =
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k
      ((D ⊔ complementaryCurveIdeal D).subschemeι ≫ gY)
      (SheafOfModules.unit (D ⊔ complementaryCurveIdeal D).subscheme.ringCatSheaf) n) : ℤ)) -
    2 * ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k fD
      (SheafOfModules.unit D.subscheme.ringCatSheaf) n) : ℤ) at hdeg
  rw [hdeg] at hpos
  rw [hP, zero_add] at hYZ
  linarith

/-- **A stable contraction factors through every chain of contractions of rational tails**, and
the second factor is again a stable contraction. Let `t : X ⟶ X_n` be a chain of contractions of
rational tails of a proper nodal curve `X` over `k` with `H⁰(X, 𝒪_X) = k`, and `c : X ⟶ Y`
satisfy the conditions of [Stacks, Tag 0E7Q], with `ω_D` invertible over `Γ(D, 𝒪_D)` for the
one-dimensional integral closed subschemes `D ⊆ Y`. Then `c = t ≫ c'` with `c'` satisfying the
same conditions for `X_n`: each contracted tail goes to a point under `c`
(`Stacks.Curves.StableModel.subsingleton_range_of_isRationalTail`), so `c` factors through the
contraction (`Stacks.Curves.StableModel.contraction_comp_eq_of_factors`), and the conditions
descend along an acyclic contraction (`Stacks.Curves.StableModel.IsStableContraction.of_comp`). -/
theorem exists_comp_eq_of_isIteratedContractionOfRationalTails {X X₁ Y : Scheme.{u}}
    {fX : X ⟶ Spec (.of k)} {f₁ : X₁ ⟶ Spec (.of k)} {t : X ⟶ X₁}
    (hseq : IsIteratedContractionOfRationalTails k fX f₁ t) (hproper : IsProper fX)
    (hdim : topologicalKrullDim X = 1) (hglob : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fX.appTop))
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨fX⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X)
    {gY : Y ⟶ Spec (.of k)} {c : X ⟶ Y} (hst : IsStableContraction fX gY c)
    (hωY : ∀ (D : Y.IdealSheafData) (_ : IsIntegral D.subscheme)
      (_ : topologicalKrullDim D.subscheme = 1),
      haveI : IsProper gY := hst.isProper
      letI : Field Γ(D.subscheme, ⊤) :=
        (isField_of_universallyClosed k (D.subschemeι ≫ gY)).toField
      haveI : IsProper D.subscheme.toSpecΓ :=
        Stacks.AlgebraicGeometry.ProperGeomConnected.isProper_toSpecΓ (D.subschemeι ≫ gY)
      SheafOfModules.IsInvertible D.subscheme.presheaf D.subscheme.ringCatSheaf.2
        (Stacks.Duality.dualizingSheafOverField D.subscheme.toSpecΓ)) :
    ∃ c' : X₁ ⟶ Y, t ≫ c' = c ∧ IsStableContraction f₁ gY c' := by
  induction hseq with
  | identity X fX => exact ⟨c, Category.id_comp c, hst⟩
  | @step X X₁ X₂ fX f₁ f₂ c₁ d C hC e hc hbase hd ih =>
    let : X.Over (Spec (.of k)) := ⟨fX⟩
    have : IsProper (X ↘ Spec (.of k)) := hproper
    have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop) := hglob
    -- the one-step chain
    have h1 : IsIteratedContractionOfRationalTails k fX f₁ (c₁ ≫ 𝟙 X₁) :=
      .step C hC e hc hbase (.identity X₁ f₁)
    have : IsProper fX := hproper
    have := hglob
    have hp₁ : IsProper f₁ := h1.isProper_target hdim hnodal
    have hdim₁ := h1.topologicalKrullDim_target hdim hnodal
    have hglob₁ := h1.isIso_globalSections_target hdim hnodal
    have hnodal₁ := h1.hasAtWorstNodalSingularities_target hdim hnodal
    have hO₁ := h1.isIso_unitToPushforwardObjUnit hdim hnodal
    have hR₁ := h1.isZero_rightDerived hdim hnodal
    rw [Category.comp_id] at hO₁ hR₁
    -- `c` contracts `C`, hence factors through `c₁`
    have hsub := subsingleton_range_of_isRationalTail k hdim hnodal hC hst hωY
    have hfac := exists_comp_eq_canonicalMapToAttachingPoint k X hC c hsub
    have hcomp := contraction_comp_eq_of_factors k X hdim hnodal hC hc c hfac
    set c₂ := e.inv ≫ complementaryCurveι C ≫ c
    have hc₂ : c₁ ≫ c₂ = c := by
      rw [← hcomp]
      simp only [c₂, Category.assoc]
    have : IsProper (c₁ ≫ f₁) := hbase ▸ hproper
    have : IsProper c₁ := IsProper.of_comp c₁ f₁
    have : CompactSpace X₁ := QuasiCompact.compactSpace_of_compactSpace f₁
    have hst₂ : IsStableContraction f₁ gY c₂ :=
      IsStableContraction.of_comp c₁ c₂ hbase hO₁ hR₁ (hc₂ ▸ hst)
    obtain ⟨c', hc', hst'⟩ := ih hp₁ hdim₁ hglob₁ hnodal₁ hst₂ hωY
    exact ⟨c', by rw [Category.assoc, hc', hc₂], hst'⟩

end Main

end Stacks.Curves.StableModel
