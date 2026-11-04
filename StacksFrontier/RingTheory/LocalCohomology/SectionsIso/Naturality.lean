module

public import StacksFrontier.RingTheory.LocalCohomology.SectionsIso.Basic

/-!
# Naturality of the sections comparison

Let `R` be a commutative ring, `f : Fin r → R` a finite family, `I = (f₁, …, f_r)` and
`U = Spec R \ V(I)`. The comparison
`Stacks.LocalCohomology.kerCechDOneEquivComplementGlobalSections` identifies the kernel of the
first differential of the extended alternating Čech complex with the sections of the associated
sheaf on `U`. This file proves it natural in the module: both sides are functors of `M`, the Čech
side through `Stacks.LocalCohomology.cechTermMap` and the sheaf side through
`Stacks.LocalCohomology.associatedAbPresheafMap`, and the comparison commutes with them.

Every step is the same two observations. A module map acts on a locally fractional section by
applying it to the numerators, so it commutes with restriction to a smaller open *by definition*;
and on a localization `M_{∏ i ∈ t, f i}` the two maps in question are both `R`-linear maps out of a
localization of `M` sending `m / 1` to `g m / 1`, so they agree by the uniqueness of maps out of a
localization.

## Main definitions

* `Stacks.LocalCohomology.moduleSectionsMap` — the action of a module map on locally fractional
  sections, as an `R`-linear map; it is `Stacks.LocalCohomology.associatedAbPresheafMap` with its
  `R`-linearity recorded.
* `Stacks.LocalCohomology.kerCechDOneMap` — the action of a module map on the degree-one Čech
  cocycles.

## Main results

* `Stacks.LocalCohomology.cechSectionsEquiv_moduleSectionsMap` — the identification
  `Γ(D(∏ i ∈ t, f i), M̃) ≅ M_{∏ i ∈ t, f i}` is natural.
* `Stacks.LocalCohomology.cechTermOneEquiv_cechTermMap` — the identification `C¹ ≅ ∏ i, M_{f_i}` is
  natural.
* `Stacks.LocalCohomology.kerCechDOneEquivComplementGlobalSections_naturality` — **the comparison
  `ker d¹ ≅ Γ(U, M̃|U)` is natural in the module**.

## References

* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite
open PrimeSpectrum (basicOpen)

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

variable {R : Type u} [CommRing R] {M N : ModuleCat.{v} R}

/-! ### The action of a module map on locally fractional sections -/

/-- The action of a module map on locally fractional sections, as an `R`-linear map: it applies the
map to the numerators, at every prime of the open. This is
`Stacks.LocalCohomology.associatedAbPresheafMap` with its `R`-linearity recorded. -/
def moduleSectionsMap (g : M ⟶ N) (U : Opens (PrimeSpectrum.Top R)) :
    moduleSections M U →ₗ[R] moduleSections N U where
  toFun s := ConcreteCategory.hom ((associatedAbPresheafMap g).app (op U)) s
  map_add' s t := map_add (ConcreteCategory.hom ((associatedAbPresheafMap g).app (op U))) s t
  map_smul' c s := Subtype.ext (funext fun x => map_smul (IsLocalizedModule.map
    x.1.asIdeal.primeCompl (LocalizedModule.mkLinearMap _ M)
    (LocalizedModule.mkLinearMap _ N) g.hom) c (s.1 x))

/-- `Stacks.LocalCohomology.moduleSectionsMap g U` agrees with the component at `U` of
`Stacks.LocalCohomology.associatedAbPresheafMap g`. -/
@[simp]
theorem moduleSectionsMap_apply (g : M ⟶ N) (U : Opens (PrimeSpectrum.Top R))
    (s : moduleSections M U) :
    moduleSectionsMap g U s = ConcreteCategory.hom ((associatedAbPresheafMap g).app (op U)) s :=
  rfl

/-- A module map commutes with restriction of sections: a section is a function on the points of
the open and the map acts pointwise. -/
theorem moduleSectionsMap_restrict (g : M ⟶ N) {U V : Opens (PrimeSpectrum.Top R)} (h : V ≤ U)
    (s : moduleSections M U) :
    moduleSectionsMap g V (moduleSectionsRestrict M h s) =
      moduleSectionsRestrict N h (moduleSectionsMap g U s) :=
  rfl

/-- A module map carries the constant fraction `m / 1` to the constant fraction `g m / 1`. -/
theorem moduleSectionsMap_comp_moduleSectionsMk (g : M ⟶ N) (U : Opens (PrimeSpectrum.Top R)) :
    (moduleSectionsMap g U).comp (moduleSectionsMk M U) =
      (moduleSectionsMk N U).comp g.hom :=
  LinearMap.ext fun _m => Subtype.ext (funext fun _x =>
    IsLocalizedModule.map_LocalizedModules _ _ _ _)

/-! ### Naturality of the comparison with the Čech localizations -/

variable {r : ℕ} (f : Fin r → R)

/-- **The identification `Γ(D(∏ i ∈ t, f i), M̃) ≅ M_{∏ i ∈ t, f i}` is natural.** Both composites
are `R`-linear maps out of a localization of `M` at the powers of `∏ i ∈ t, f i` sending the
constant fraction `m / 1` to `g m / 1`. -/
theorem cechSectionsEquiv_comp_moduleSectionsMap (g : M ⟶ N) (t : Finset (Fin r)) :
    (cechSectionsEquiv f N t).toLinearMap.comp (moduleSectionsMap g (cechBasicOpen f t)) =
      (cechModMap f g t).comp (cechSectionsEquiv f M t).toLinearMap := by
  refine IsLocalizedModule.ext (Cech.cechSub f t) (moduleSectionsMk M (cechBasicOpen f t))
    (fun x => Cech.isUnit_algebraMap f (N : Type _) (le_refl t)
      (LocalizedModule.mkLinearMap (Cech.cechSub f t) (N : Type _)) x) ?_
  refine LinearMap.ext fun m => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [show moduleSectionsMap g (cechBasicOpen f t) (moduleSectionsMk M (cechBasicOpen f t) m) =
      moduleSectionsMk N (cechBasicOpen f t) (g m) from
    LinearMap.congr_fun (moduleSectionsMap_comp_moduleSectionsMk g (cechBasicOpen f t)) m]
  rw [cechSectionsEquiv_moduleSectionsMk, cechSectionsEquiv_moduleSectionsMk,
    cechModMap_mkLinearMap]

/-- `Stacks.LocalCohomology.cechSectionsEquiv_comp_moduleSectionsMap`, applied to a section. -/
theorem cechSectionsEquiv_moduleSectionsMap (g : M ⟶ N) (t : Finset (Fin r))
    (s : moduleSections M (cechBasicOpen f t)) :
    cechSectionsEquiv f N t (moduleSectionsMap g (cechBasicOpen f t) s) =
      cechModMap f g t (cechSectionsEquiv f M t s) :=
  LinearMap.congr_fun (cechSectionsEquiv_comp_moduleSectionsMap f g t) s

/-! ### Naturality of the degree-one coordinates -/

/-- **The identification `C¹ ≅ ∏ i, M_{f_i}` is natural.** The induced map on the Čech term acts on
each summand separately, so it acts on each coordinate separately. -/
theorem cechTermOneEquiv_cechTermMap (g : M ⟶ N) (x : Cech.cechTerm f (M : Type _) 1) (i : Fin r) :
    cechTermOneEquiv f N (cechTermMap f g 1 x) i =
      cechModMap f g {i} (cechTermOneEquiv f M x i) := by
  simp only [cechTermOneEquiv_apply]
  refine DirectSum.induction_on x ?_ (fun s m => ?_) (fun u v hu hv => ?_)
  · simp only [map_zero]
  on_goal 2 =>
    simp only [map_add]
    rw [hu, hv]
  rw [← DirectSum.lof_eq_of R, cechTermMap_lof]
  by_cases hs : s.1 = {i}
  · rw [cechComponent_lof_of_eq f N _ _ hs, cechComponent_lof_of_eq f M _ _ hs,
      cechι_cechModMap]
  · rw [cechComponent_lof_of_ne f N _ _ hs, cechComponent_lof_of_ne f M _ _ hs, map_zero]

/-- The action of a module map on the degree-one Čech cocycles: the induced map on the Čech term
commutes with the differential, so it preserves the kernel. -/
def kerCechDOneMap (g : M ⟶ N) :
    LinearMap.ker (Cech.cechD f (M : Type _) 1) →ₗ[R]
      LinearMap.ker (Cech.cechD f (N : Type _) 1) :=
  (cechTermMap f g 1).restrict fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply, cechTermMap_comp_cechD, LinearMap.comp_apply, hx, map_zero]

/-- The underlying Čech cochain of the image of a cocycle `x` under
`Stacks.LocalCohomology.kerCechDOneMap f g` is the image of `x` under `cechTermMap f g 1`. -/
@[simp]
theorem kerCechDOneMap_coe (g : M ⟶ N) (x : LinearMap.ker (Cech.cechD f (M : Type _) 1)) :
    (kerCechDOneMap f g x).1 = cechTermMap f g 1 x.1 :=
  LinearMap.coe_restrict_apply _ _

/-! ### Naturality of the full comparison -/

/-- Restriction of locally fractional sections is transitive: a section is a function on the points
of the open, and both composites read off its value at the same points. -/
theorem moduleSectionsRestrict_restrict {U V W : Opens (PrimeSpectrum.Top R)} (h₁ : V ≤ U)
    (h₂ : W ≤ V) (s : moduleSections M U) :
    moduleSectionsRestrict M h₂ (moduleSectionsRestrict M h₁ s) =
      moduleSectionsRestrict M (h₂.trans h₁) s :=
  rfl

variable (I : Ideal R)

/-- Each standard open of the cover of `U = Spec R \ V(I)` lies in the image of the top open under
the open immersion of `U`. -/
theorem cechBasicOpen_le_ι_image_top (hIf : Ideal.span (Set.range f) = I) (i : Fin r) :
    cechBasicOpen f {i} ≤ (complementZeroLocus R I).ι ''ᵁ ⊤ :=
  (le_iSup (fun j => cechBasicOpen f {j}) i).trans
    ((complementZeroLocus_eq_iSup_cechBasicOpen f I hIf).ge.trans
      (Scheme.Opens.ι_image_top (complementZeroLocus R I)).ge)

/-- **What the comparison `ker d¹ ≅ Γ(U, M̃|U)` does.** The section attached to a degree-one Čech
cocycle restricts on the standard open `D(f_i)` to the `i`-th coordinate of the cocycle. This
characterizes the comparison, the `D(f_i)` covering `U`. -/
theorem cechSectionsEquiv_restrict_kerCechDOneEquiv (hIf : Ideal.span (Set.range f) = I)
    (x : LinearMap.ker (Cech.cechD f (M : Type _) 1)) (i : Fin r) :
    cechSectionsEquiv f M {i} (moduleSectionsRestrict M (cechBasicOpen_le_ι_image_top f I hIf i)
        (kerCechDOneEquivComplementGlobalSections I M f hIf x)) =
      cechTermOneEquiv f M x.1 i :=
  congrFun (congrArg (fun z : cechCompatible f M => z.1)
    ((moduleSectionsComplementEquivCechCompatible f M I hIf).apply_symm_apply
      ⟨cechTermOneEquiv f M x.1, (mem_ker_cechD_one_iff f M x.1).1 x.2⟩)) i

/-- **The comparison `ker d¹ ≅ Γ(U, M̃|U)` is natural in the module.** The two sections it produces
have the same restriction to every standard open `D(f_i)` of the cover, because on `D(f_i)` each is
the image under `g` of the `i`-th coordinate of the cocycle; and the `D(f_i)` cover `U`. -/
theorem kerCechDOneEquivComplementGlobalSections_naturality
    (hIf : Ideal.span (Set.range f) = I) (g : M ⟶ N)
    (x : LinearMap.ker (Cech.cechD f (M : Type _) 1)) :
    kerCechDOneEquivComplementGlobalSections I N f hIf (kerCechDOneMap f g x) =
      (associatedAbPresheafMap g).app (op ((complementZeroLocus R I).ι ''ᵁ ⊤))
        (kerCechDOneEquivComplementGlobalSections I M f hIf x) := by
  refine Subtype.ext (funext fun p => ?_)
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
    ((complementZeroLocus_eq_iSup_cechBasicOpen f I hIf).le
      ((Scheme.Opens.ι_image_top (complementZeroLocus R I)).le p.2))
  have hL := cechSectionsEquiv_restrict_kerCechDOneEquiv (M := N) f I hIf (kerCechDOneMap f g x) i
  rw [kerCechDOneMap_coe, cechTermOneEquiv_cechTermMap] at hL
  have hR : cechSectionsEquiv f N {i} (moduleSectionsRestrict N
        (cechBasicOpen_le_ι_image_top f I hIf i) (moduleSectionsMap g
          ((complementZeroLocus R I).ι ''ᵁ ⊤)
          (kerCechDOneEquivComplementGlobalSections I M f hIf x))) =
      cechModMap f g {i} (cechTermOneEquiv f M x.1 i) :=
    ((congrArg (cechSectionsEquiv f N {i}) (moduleSectionsMap_restrict g
          (cechBasicOpen_le_ι_image_top f I hIf i)
          (kerCechDOneEquivComplementGlobalSections I M f hIf x)).symm).trans
        (cechSectionsEquiv_moduleSectionsMap f g {i} _)).trans
      (congrArg (cechModMap f g {i})
        (cechSectionsEquiv_restrict_kerCechDOneEquiv f I hIf x i))
  exact congrFun (congrArg Subtype.val
    ((cechSectionsEquiv f N {i}).injective (hL.trans hR.symm))) ⟨p.1, hi⟩

end Stacks.LocalCohomology

end
