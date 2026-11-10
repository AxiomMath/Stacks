module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularIdealSheaf.RegularToQuasiRegular
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.ZeroScheme
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.Comap
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.Immersions
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.SlicingHypotheses
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.Lifting
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Immersion

/-!
# Slicing a flat morphism by a regular sequence

Let `f : X ⟶ S` be locally of finite presentation and flat at `x : X`, and let `h₁, …, h_r` be
elements of the local ring `𝒪_{X, x}` whose images in the local ring of the fibre `X_{f x}` at
`x` form a regular sequence.  Then `h₁, …, h_r` are the germs of global sections `a₁, …, a_r` of
an affine open neighbourhood `U` of `x`, and the zero scheme `V(a)` of those sections is a
regular immersion into `U`, is flat and locally of finite presentation over `S`, and stays a
regular immersion after any change of base.

This is Stacks tag 06LI, conditional on `Stacks.AlgebraicGeometry.Statement063I` and
`Stacks.AlgebraicGeometry.Statement063W`, the statements of Stacks tags 063I and 063W, which are
taken as hypotheses.

## Main results

* `Stacks.AlgebraicGeometry.exists_open_relativeQuasiRegular_ofIdealTop`: on an affine scheme
  flat over the base, the zero scheme of a family of global sections whose germs are regular on
  the fibre is a relative quasi-regular and regular immersion near the point.
* `Stacks.AlgebraicGeometry.exists_affineOpen_regularImmersion_of_isRegular_fiber`: Stacks tag
  06LI, conditional on `Statement063I` and `Statement063W`.

## References

* [Stacks Project, Lemma 37.24.1 (Tag 06LI)](https://stacks.math.columbia.edu/tag/06LI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open RingTheory.Sequence

open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace Stacks.AlgebraicGeometry

universe u

/-- The zero scheme of finitely many global sections of an affine scheme is locally of finite
presentation over it. -/
private theorem locallyOfFinitePresentation_subschemeι_ofIdealTop_ofList {X : Scheme.{u}}
    [IsAffine X] (l : List Γ(X, ⊤)) :
    LocallyOfFinitePresentation (Scheme.IdealSheafData.ofIdealTop (Ideal.ofList l)).subschemeι :=
  locallyOfFinitePresentation_subschemeι_ofIdealTop _ (Submodule.fg_span (List.finite_toSet _))

/-- **The affine heart of Stacks tag 06LI.**  Let `X` be affine, flat and locally of finite
presentation over `S`, let `a : Fin r → Γ(X, ⊤)` and let `x : X` be a point at which the germs of
`a` are a regular sequence in the local ring of the fibre.  Then `x` lies on the zero scheme
`V(a)`, and on some open neighbourhood of `x` the zero scheme is a relative quasi-regular
immersion over `S` and a regular immersion.

Conditional on `Statement063I` and `Statement063W`. -/
theorem exists_open_relativeQuasiRegular_ofIdealTop (h063I : Statement063I.{u})
    (h063W : Statement063W.{u}) {X S : Scheme.{u}} [IsAffine X] (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] (x : X) {r : ℕ} (a : Fin r → Γ(X, ⊤))
    (hr : IsRegular ((f.fiber (f x)).presheaf.stalk (f.asFiber x))
      (List.ofFn fun j => ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom
        ((f.fiberι_asFiber x).symm ▸ X.presheaf.germ ⊤ x trivial (a j)))) :
    x ∈ (Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn a))).support ∧
      ∃ U : X.Opens, x ∈ U ∧
        IsRelativeQuasiRegularImmersion (U.ι ≫ f)
            ((Scheme.IdealSheafData.ofIdealTop
              (Ideal.ofList (List.ofFn a))).comap U.ι).subschemeι ∧
          IsRegularImmersion ((Scheme.IdealSheafData.ofIdealTop
            (Ideal.ofList (List.ofFn a))).comap U.ι).subschemeι := by
  set T := Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn a)) with hT
  set l : List (X.presheaf.stalk x) := List.ofFn fun j => X.presheaf.germ ⊤ x trivial (a j)
    with hl
  obtain ⟨hreg, hquot⟩ := isRegular_stalk_and_flatQuotients_of_isRegular_fiber f x
    (Flat.stalkMap f x) (fun j => X.presheaf.germ ⊤ x trivial (a j)) hr
  have hlmap : (List.ofFn a).map (X.presheaf.germ ⊤ x trivial) = l := by
    rw [hl, List.map_ofFn]; rfl
  have hreg' : IsRegular (X.presheaf.stalk x)
      ((List.ofFn a).map (X.presheaf.germ ⊤ x trivial)) := by rwa [hlmap]
  have hx := mem_support_ofIdealTop_of_isRegular_germ x (List.ofFn a) hreg'
  have hsmul : Ideal.ofList (l.take r) •
      (⊤ : Submodule (X.presheaf.stalk x) (X.presheaf.stalk x)) =
      (Ideal.ofList l : Submodule (X.presheaf.stalk x) (X.presheaf.stalk x)) := by
    rw [List.take_of_length_le (by simp [hl]), Ideal.smul_top_eq_map]
    exact Ideal.map_id (Ideal.ofList l)
  have hq := hquot r
  rw [hsmul] at hq
  have hq' : ((Ideal.Quotient.mk (Ideal.ofList
      ((List.ofFn a).map (X.presheaf.germ ⊤ x trivial)))).comp (f.stalkMap x).hom).Flat := by
    rwa [hlmap]
  have hflat := flat_stalkMap_subschemeι_comp_of_flat_quotient f (List.ofFn a) x hx hq'
  have hNoeth : IsLocallyNoetherian (f.fiber (f x)) := isLocallyNoetherian_fiber f (f x)
  set b : List Γ(f.fiber (f x), ⊤) := (List.ofFn a).map (f.fiberι (f x)).appTop.hom with hb
  have hregFib : IsRegular ((f.fiber (f x)).presheaf.stalk (f.asFiber x))
      ((List.ofFn a).map ((f.fiberι (f x)).appTop ≫
        (f.fiber (f x)).presheaf.germ ⊤ (f.asFiber x) trivial)) := by
    simpa only [List.map_ofFn, Function.comp_def, germ_fiberι_appTop_apply] using hr
  have hregFib' : IsRegular ((f.fiber (f x)).presheaf.stalk (f.asFiber x))
      (b.map ((f.fiber (f x)).presheaf.germ ⊤ (f.asFiber x) trivial)) := by
    rwa [hb, List.map_map]
  obtain ⟨V, hxV, hqr⟩ := h063I hNoeth b (f.asFiber x) hregFib'
  have hcomap : T.comap (f.fiberι (f x)) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.ofList b) := by
    rw [hT, comap_ofIdealTop, Ideal.map_ofList, hb]
  have hquasi : ∃ W : (f.fiber (f x)).Opens, f.asFiber x ∈ W ∧ IsQuasiRegularImmersion
      (((T.comap (f.fiberι (f x))).comap W.ι).subschemeι) := by
    rw [hcomap]; exact ⟨V, hxV, hqr⟩
  exact ⟨hx, h063W f inferInstance inferInstance T
    (locallyOfFinitePresentation_subschemeι_ofIdealTop_ofList _) x hx hquasi hflat⟩

/-- **Stacks Project, Lemma 37.24.1 (Tag 06LI), conditionally.**  Let `f : X ⟶ S` be locally of
finite presentation and flat at `x : X`, and let `h : Fin r → 𝒪_{X, x}` be a family whose image
in the local ring of the fibre `X_{f x}` at `x` is a regular sequence.  Then there is an affine
open `U` containing `x` and global sections `a : Fin r → Γ(U, ⊤)` whose germs at `x` are the
`h i`, such that `x` lies on the zero scheme `V(a)`, the closed immersion of `V(a)` into `U` is
a regular immersion, `V(a)` is flat and locally of finite presentation over `S`, and the base
change of the immersion along any `S' ⟶ S` is again a regular immersion.

The hypotheses `h063I` and `h063W` are the statements of Stacks tags 063I and 063W. -/
theorem exists_affineOpen_regularImmersion_of_isRegular_fiber (h063I : Statement063I.{u})
    (h063W : Statement063W.{u}) {X S : Scheme.{u}} (f : X ⟶ S) (x : X) {r : ℕ}
    (h : Fin r → X.presheaf.stalk x) [LocallyOfFinitePresentation f]
    (hflat : IsFlatAt f.toLRSHom.toShHom x)
    (hregular : RingTheory.Sequence.IsRegular
      ((f.fiber (f x)).presheaf.stalk (f.asFiber x))
      (List.ofFn fun i : Fin r =>
        ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom ((f.fiberι_asFiber x).symm ▸ h i))) :
    ∃ (U : X.affineOpens) (hx : x ∈ U.1) (a : Fin r → Γ(U.1.toScheme, ⊤)),
      let y : U.1.toScheme := ⟨x, hx⟩
      let I : U.1.toScheme.IdealSheafData :=
        Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn a))
      (∀ i : Fin r, (U.1.ι.stalkMap y).hom ((show U.1.ι y = x by rfl).symm ▸ h i) =
          U.1.toScheme.presheaf.germ ⊤ y (by trivial) (a i)) ∧
      y ∈ I.support ∧
      IsRegularImmersion I.subschemeι ∧
      Flat (I.subschemeι ≫ U.1.ι ≫ f) ∧
      LocallyOfFinitePresentation (I.subschemeι ≫ U.1.ι ≫ f) ∧
      ∀ (S' : Scheme.{u}) (g : S' ⟶ S),
        IsRegularImmersion (pullback.snd I.subschemeι (pullback.fst (U.1.ι ≫ f) g)) := by
  classical
  obtain ⟨U, hxU, a, hUf, ha⟩ := exists_affineOpen_lifts_of_isFlatAt f x h hflat
  have hUaff : IsAffine U.1.toScheme := U.2
  have hfUflat : Flat (U.1.ι ≫ f) := hUf
  have hrU := isRegular_fiber_comp_of_isOpenImmersion U.1.ι f (⟨x, hxU⟩ : U.1.toScheme) h hregular
  have hrUa : IsRegular
      (((U.1.ι ≫ f).fiber ((U.1.ι ≫ f) (⟨x, hxU⟩ : U.1.toScheme))).presheaf.stalk
        ((U.1.ι ≫ f).asFiber (⟨x, hxU⟩ : U.1.toScheme)))
      (List.ofFn fun j => (((U.1.ι ≫ f).fiberι
            ((U.1.ι ≫ f) (⟨x, hxU⟩ : U.1.toScheme))).stalkMap
          ((U.1.ι ≫ f).asFiber (⟨x, hxU⟩ : U.1.toScheme))).hom
        (((U.1.ι ≫ f).fiberι_asFiber (⟨x, hxU⟩ : U.1.toScheme)).symm ▸
          U.1.toScheme.presheaf.germ ⊤ (⟨x, hxU⟩ : U.1.toScheme) trivial (a j))) := by
    simp only [← ha]
    exact hrU
  obtain ⟨hyT, O, hyO, hrel, hreg⟩ := exists_open_relativeQuasiRegular_ofIdealTop h063I h063W
    (U.1.ι ≫ f) (⟨x, hxU⟩ : U.1.toScheme) a hrUa
  set T := Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn a)) with hT
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (⟨⟨x, hxU⟩, hyO, rfl⟩ : x ∈ U.1.ι ''ᵁ O) (U.1.ι ''ᵁ O).isOpen
  let Va : X.affineOpens := ⟨V, hV⟩
  have hVaff : IsAffine Va.1.toScheme := hV
  have hVU : Va.1 ≤ U.1 := fun t ht => by
    obtain ⟨z, _, rfl⟩ := hVW ht
    exact z.property
  let jv := X.homOfLE hVU
  have hjι : jv ≫ U.1.ι = Va.1.ι := X.homOfLE_ι hVU
  have hjvO : Set.range jv ⊆ Set.range O.ι := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨w, hw, hwz⟩ := hVW z.property
    refine ⟨⟨w, hw⟩, U.1.ι.isOpenEmbedding.injective ?_⟩
    change w.val = (jv z).val
    rwa [show (jv z).val = z.val from X.homOfLE_apply hVU z]
  let kv := IsOpenImmersion.lift O.ι jv hjvO
  have hkO : kv ≫ O.ι = jv := IsOpenImmersion.lift_fac _ _ _
  have hkOI : IsOpenImmersion kv := by
    have hco : IsOpenImmersion (kv ≫ O.ι) := hkO.symm ▸ inferInstance
    exact IsOpenImmersion.of_comp kv O.ι
  let b : Fin r → Γ(Va.1.toScheme, ⊤) := fun t => jv.appTop (a t)
  set I := Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn b)) with hI
  have hTj : T.comap jv = I := by
    rw [hT, hI, comap_ofIdealTop, Ideal.map_ofList, List.map_ofFn]
    rfl
  have hTkO : (T.comap O.ι).comap kv = I := by
    rw [← Scheme.IdealSheafData.comap_comp, hkO, hTj]
  have hregI : IsRegularImmersion I.subschemeι := by
    rw [← hTkO]
    exact isRegularImmersion_comap_of_isOpenImmersion (T.comap O.ι) kv hreg
  have hflatO : Flat ((T.comap O.ι).subschemeι ≫ O.ι ≫ U.1.ι ≫ f) := hrel.1
  have hflatI : Flat (I.subschemeι ≫ Va.1.ι ≫ f) := by
    have hh := flat_comap_of_isOpenImmersion (T.comap O.ι) (O.ι ≫ U.1.ι ≫ f) kv
    rw [hTkO] at hh
    simpa only [← Category.assoc, hkO, hjι] using hh
  have hflatV : Flat (Va.1.ι ≫ f) := by
    simpa only [← Category.assoc, hjι] using (inferInstance : Flat (jv ≫ U.1.ι ≫ f))
  have hlfpI : LocallyOfFinitePresentation I.subschemeι :=
    locallyOfFinitePresentation_subschemeι_ofIdealTop_ofList _
  have hjz : jv (⟨x, hxV⟩ : Va.1.toScheme) = (⟨x, hxU⟩ : U.1.toScheme) :=
    Subtype.ext (X.homOfLE_apply hVU _)
  have hgerm (t : Fin r) : (Va.1.ι.stalkMap (⟨x, hxV⟩ : Va.1.toScheme)).hom
      ((show Va.1.ι (⟨x, hxV⟩ : Va.1.toScheme) = x by rfl).symm ▸ h t) =
      Va.1.toScheme.presheaf.germ ⊤ (⟨x, hxV⟩ : Va.1.toScheme) (by trivial) (b t) :=
    germ_comp_of_lift_of_eq U.1.ι jv Va.1.ι hjι ⟨x, hxV⟩ hjz rfl (h t) (a t) (ha t)
  have hsupp : (⟨x, hxV⟩ : Va.1.toScheme) ∈ I.support := by
    rw [← hTj, Scheme.IdealSheafData.support_comap]
    change jv (⟨x, hxV⟩ : Va.1.toScheme) ∈ T.support
    rwa [hjz]
  have hbc (S' : Scheme.{u}) (g : S' ⟶ S) :
      IsRegularImmersion (pullback.snd I.subschemeι (pullback.fst (Va.1.ι ≫ f) g)) :=
    isRegularImmersion_pullback_snd_of_isRelativeQuasiRegular (Va.1.ι ≫ f) I.subschemeι
      ⟨hflatI, isQuasiRegularImmersion_of_isRegularImmersion _ hregI⟩ g
  exact ⟨Va, hxV, b, hgerm, hsupp, hregI, hflatI, inferInstance, hbc⟩

end Stacks.AlgebraicGeometry

end
