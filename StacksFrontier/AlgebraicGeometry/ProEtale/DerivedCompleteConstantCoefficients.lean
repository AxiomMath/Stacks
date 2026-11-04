module

public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedNakayamaProEtale
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleComplexes
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafBaseChange
public import StacksFrontier.CategoryTheory.Sites.Sheaf.HasSheafComposeForgetRing

/-!
# Derived Nakayama for constant coefficients on the small pro-étale site

[Stacks, Tag 09BY] reads: let `X` be a scheme, let `Λ` be a ring with a finitely generated
ideal `I ⊂ Λ`, and let `ℱ` be a sheaf of `Λ`-modules on `X_proétale`; if `ℱ` is derived
complete and `ℱ/Iℱ = 0`, then `ℱ = 0`. This file states exactly that, at the tag's own objects:
`AlgebraicGeometry.ProEtale.isZero_of_isDerivedComplete_constantCoefficients`.

`AlgebraicGeometry.ProEtale.isZero_of_isDerivedComplete_proetale` already reads the chapter's
lemma at the small pro-étale site, but for an *arbitrary* sheaf of rings `𝒪` and an arbitrary
sheaf of ideals `ℐ` carrying a finite-generation hypothesis on sections. Specializing it to the
tag's constant coefficients means producing that hypothesis for the constant ideal sheaf
`AlgebraicGeometry.ProEtale.constantCoefficientIdealSheaf`, and that is what the bulk of this
file does.

## Main results

* `AlgebraicGeometry.ProEtale.fg_constantCoefficientIdealSheaf_obj`: the sections of the
  constant coefficient ideal sheaf over any object of the site are finitely generated, as soon
  as `I` is — the hypothesis `hI` of [Stacks, Tag 09BY], with no Noetherian hypothesis on `Λ`.
* `AlgebraicGeometry.ProEtale.isZero_of_isDerivedComplete_constantCoefficients`:
  **[Stacks, Tag 09BY]** at the tag's own objects.

## Implementation notes

**The gap that had to be bridged.** `Stacks.ConstantSheaf.fg_ker_constantSheaf_ringCatMap_app`
computes the sectionwise kernel of a map of constant sheaves of rings and finds it finitely
generated from `(ker π).FG` alone. It is stated for
`(constantSheaf J RingCat).map (RingCat.ofHom π)`, the sheafification of the constant presheaf
of *rings*. The ideal sheaf the consumer has is the kernel of
`AlgebraicGeometry.ProEtale.constantCoefficientRingReduction`, which is the sheafification of
the constant presheaf of *commutative* rings, composed afterwards with
`forget₂ CommRingCat RingCat`. Those are different sheaves — not two spellings of one term — so
the finite-generation lemma does not apply on the nose; the two must first be identified.

The identification is `CategoryTheory.constantCommuteCompose` for
`forget₂ CommRingCat RingCat`, available because
`Stacks.instPreservesSheafificationForget₂CommRingCatRingCat` supplies the
`PreservesSheafification` hypothesis it needs. Its naturality square carries
`constantCoefficientRingReduction` to the `RingCat` constant-sheaf map, and
`AlgebraicGeometry.ProEtale.ker_app_eq_comap` turns that square into an identification of
sectionwise kernels: the one is the comap of the other along a ring isomorphism. Finite
generation then transports by `AlgebraicGeometry.ProEtale.fg_comap_of_inverse`.

**No Noetherian hypothesis.** Only `I.FG` is used, matching the source. The route through
[Stacks, Tag 093M] at a finitely presented module, which would force `Λ` Noetherian, is not
taken: the finite-generation input is the `_of_fg` form in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafBaseChange`. The adjacent
[Stacks, Tag 09BZ] does assume `Λ` Noetherian; that hypothesis is absent here.

**Instances that must be named.** Two `PreservesSheafification` instances for
`forget₂ (ModuleCat _) AddCommGrpCat` are supplied by name through
`AlgebraicGeometry.ProEtale.preservesSheafification_forget₂_moduleCat`: typeclass search for
them exhausts its heartbeat budget, exactly as recorded for
`forget₂ CommRingCat RingCat` in
`StacksFrontier.CategoryTheory.Sites.Sheaf.HasSheafComposeForgetRing`. The two universe-pinned
sheafification instances of
`StacksFrontier.AlgebraicGeometry.ProEtale.DerivedNakayamaProEtale` are made local instances here
for the same reason given there.

**Universes.** The coefficient ring is taken in the scheme's own universe, `Λ : Type u` for
`X : Scheme.{u}`. The chapter's derived-completeness statements are pinned at value universe
`u + 1`, so `AlgebraicGeometry.ProEtale.constantCoefficientRingedSite.{u, r, w}` can be used
here only for `r ≤ u + 1`; the coefficient universe cannot be left free. The same proof reads
verbatim at `Λ : Type (u + 1)`.

**Generality of the helpers.** `fg_comap_of_inverse`, `app_comp_app`, `app_leftInverse`,
`app_rightInverse`, `ker_app_eq_comap` and `preservesSheafification_forget₂_moduleCat` are
general and have nothing to do with the pro-étale site; they live here because this is their
only consumer so far.

## References

* [Stacks Project, Tag 09BY](https://stacks.math.columbia.edu/tag/09BY)
* [Stacks Project, Tag 093J](https://stacks.math.columbia.edu/tag/093J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
  SheafOfModules.hasSheafify_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.ProEtale.hasSheafify_proetale_addCommGrpCat_succ
  AlgebraicGeometry.ProEtale.wEqualsLocallyBijective_proetale_addCommGrpCat_succ

universe u v w

namespace AlgebraicGeometry.ProEtale

/-- Sheafification of presheaves of modules is compatible with forgetting to abelian groups,
on a site whose objects and morphisms are no larger than the module universe.

This is Mathlib's instance for a functor between concrete categories, at the one size where it
needs no `UnivLE` gymnastics. It has to be supplied by name: typeclass search for
`J.PreservesSheafification (forget₂ (ModuleCat R) AddCommGrpCat)` exhausts the
20000-heartbeat `synthInstance` budget, for the reason recorded in
`StacksFrontier.CategoryTheory.Sites.Sheaf.HasSheafComposeForgetRing` for
`forget₂ CommRingCat RingCat`. -/
theorem preservesSheafification_forget₂_moduleCat {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (R : Type (max u v)) [Ring R] :
    J.PreservesSheafification
      (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}) :=
  GrothendieckTopology.instPreservesSheafification J _

/-- Finite generation of an ideal transports along the preimage of a ring homomorphism with a
two-sided inverse. -/
theorem fg_comap_of_inverse {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (g : S →+* R) (hgf : Function.LeftInverse g f)
    (hfg : Function.LeftInverse f g) {I : Ideal S} (h : I.FG) : (I.comap f).FG := by
  have he : I.comap f = I.map g :=
    le_antisymm (Ideal.comap_le_map_of_inverse f g I hgf)
      (Ideal.map_le_comap_of_inverse g f I hfg)
  rw [he]
  exact h.map _

section SheafIso

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The two directions of an isomorphism of sheaves of rings compose to the identity on
sections over any object. -/
theorem app_comp_app {A B : Sheaf J RingCat.{w}} (e : A ≅ B) (W : Cᵒᵖ) :
    (e.hom.hom.app W) ≫ (e.inv.hom.app W) = 𝟙 (A.obj.obj W) :=
  calc (e.hom.hom.app W) ≫ (e.inv.hom.app W)
      = ((e.hom ≫ e.inv).hom.app W) := rfl
    _ = ((𝟙 A : A ⟶ A).hom.app W) := by rw [e.hom_inv_id]
    _ = 𝟙 (A.obj.obj W) := rfl

/-- `AlgebraicGeometry.ProEtale.app_comp_app` as an identity of ring homomorphisms. -/
theorem app_comp_hom {A B : Sheaf J RingCat.{w}} (e : A ≅ B) (W : Cᵒᵖ) :
    (e.inv.hom.app W).hom.comp (e.hom.hom.app W).hom = RingHom.id _ :=
  congrArg RingCat.Hom.hom (app_comp_app e W)

/-- Sections of the inverse of an isomorphism of sheaves of rings are a left inverse of the
sections of the isomorphism. -/
theorem app_leftInverse {A B : Sheaf J RingCat.{w}} (e : A ≅ B) (W : Cᵒᵖ) :
    Function.LeftInverse (e.inv.hom.app W).hom (e.hom.hom.app W).hom :=
  fun x => RingHom.congr_fun (app_comp_hom e W) x

/-- Sections of an isomorphism of sheaves of rings are a left inverse of the sections of its
inverse. -/
theorem app_rightInverse {A B : Sheaf J RingCat.{w}} (e : A ≅ B) (W : Cᵒᵖ) :
    Function.LeftInverse (e.hom.hom.app W).hom (e.inv.hom.app W).hom :=
  app_leftInverse e.symm W

/-- **Transport of a sectionwise kernel along a commuting square.** In a commuting square of
sheaves of rings whose two verticals are isomorphisms, the sectionwise kernel of one horizontal
is the preimage, along the vertical, of the sectionwise kernel of the other. -/
theorem ker_app_eq_comap {A B A' B' : Sheaf J RingCat.{w}}
    (α : A ⟶ B) (β : A' ⟶ B') (i : A ≅ A') (j : B ≅ B')
    (h : α ≫ j.hom = i.hom ≫ β) (W : Cᵒᵖ) :
    RingHom.ker (α.hom.app W).hom
      = Ideal.comap (i.hom.hom.app W).hom (RingHom.ker (β.hom.app W).hom) := by
  have hx : ∀ x, (j.hom.hom.app W).hom ((α.hom.app W).hom x)
      = (β.hom.app W).hom ((i.hom.hom.app W).hom x) := fun x =>
    congrArg (fun φ : A.obj.obj W ⟶ B'.obj.obj W => RingCat.Hom.hom φ x)
      (congrArg (fun γ : A ⟶ B' => γ.hom.app W) h)
  ext x
  simp only [RingHom.mem_ker, Ideal.mem_comap]
  constructor
  · intro hk
    rw [← hx x, hk, map_zero]
  · intro hk
    exact (app_leftInverse j W).injective (by rw [hx x, hk, map_zero])

end SheafIso

/-- Reduction modulo `I` on the universe-lifted coefficients, the ring homomorphism underlying
`AlgebraicGeometry.ProEtale.constantCoefficientReduction`. -/
def liftedQuotientMk (Λ : Type u) [CommRing Λ] (I : Ideal Λ) :
    ULift.{u + 1} Λ →+* ULift.{u + 1} (Λ ⧸ I) :=
  (ULift.ringEquiv.{u, u + 1} (R := Λ ⧸ I)).symm.toRingHom.comp
    ((Ideal.Quotient.mk I).comp (ULift.ringEquiv.{u, u + 1} (R := Λ)).toRingHom)

/-- The kernel of reduction on the lifted coefficients is finitely generated as soon as `I` is:
it is the preimage of `I` under the universe-lifting ring equivalence. -/
theorem fg_ker_liftedQuotientMk (Λ : Type u) [CommRing Λ] (I : Ideal Λ) (hI : I.FG) :
    (RingHom.ker (liftedQuotientMk Λ I)).FG := by
  have h : RingHom.ker (liftedQuotientMk Λ I)
      = I.comap (ULift.ringEquiv.{u, u + 1} (R := Λ) : ULift.{u + 1} Λ →+* Λ) := by
    ext x
    simp [liftedQuotientMk, RingHom.mem_ker, Ideal.mem_comap,
      Ideal.Quotient.eq_zero_iff_mem]
  rw [h]
  refine fg_comap_of_inverse _ (ULift.ringEquiv.{u, u + 1} (R := Λ)).symm.toRingHom ?_ ?_ hI
  · exact (ULift.ringEquiv.{u, u + 1} (R := Λ)).symm_apply_apply
  · exact (ULift.ringEquiv.{u, u + 1} (R := Λ)).apply_symm_apply

/-- **The finite-generation hypothesis of [Stacks, Tag 09BY] for constant coefficients.** The
sections, over any object of the small pro-étale site, of the ideal sheaf cut out by a finitely
generated ideal `I ⊂ Λ` in the constant coefficient ring sheaf are finitely generated over the
sections of that ring sheaf.

Nothing beyond `I.FG` is assumed of `Λ`. The proof identifies this ideal sheaf — a kernel of
constant sheaves of `CommRingCat` read in `RingCat` — with the kernel of the corresponding map
of `RingCat` constant sheaves, along `CategoryTheory.constantCommuteCompose`, and then applies
`Stacks.ConstantSheaf.fg_ker_constantSheaf_ringCatMap_app`. -/
theorem fg_constantCoefficientIdealSheaf_obj (X : Scheme.{u}) (Λ : Type u) [CommRing Λ]
    (I : Ideal Λ) (hI : I.FG) (W : X.ProEt) :
    ((constantCoefficientIdealSheaf.{u, u, u} X Λ I).toSubmodule.obj (op W)).FG := by
  let : (Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} Λ)) AddCommGrpCat.{u + 1}) :=
    preservesSheafification_forget₂_moduleCat _ _
  let : (Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (Λ ⧸ I))) AddCommGrpCat.{u + 1}) :=
    preservesSheafification_forget₂_moduleCat _ _
  have hobj : (constantCoefficientIdealSheaf.{u, u, u} X Λ I).toSubmodule.obj (op W)
      = RingHom.ker ((constantCoefficientRingReduction.{u, u, u} X Λ I).hom.app (op W)).hom :=
    SheafOfModules.kerIdeal_obj _ _
  let e := constantCommuteCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  rw [hobj, ker_app_eq_comap
    (constantCoefficientRingReduction.{u, u, u} X Λ I)
    ((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).map
      (RingCat.ofHom (liftedQuotientMk Λ I)))
    (e.app (CommRingCat.of (ULift.{u + 1} Λ)))
    (e.app (CommRingCat.of (ULift.{u + 1} (Λ ⧸ I))))
    (e.hom.naturality (CommRingCat.ofHom (liftedQuotientMk Λ I))) (op W)]
  refine fg_comap_of_inverse _ _ (app_leftInverse _ (op W)) (app_rightInverse _ (op W)) ?_
  exact Stacks.ConstantSheaf.fg_ker_constantSheaf_ringCatMap_app (Scheme.ProEt.topology X)
    (liftedQuotientMk Λ I) _ rfl (fg_ker_liftedQuotientMk Λ I hI) W

/-- **[Stacks, Tag 09BY].** Let `X` be a scheme, let `Λ` be a ring with a finitely generated
ideal `I ⊂ Λ`, and let `ℱ` be a sheaf of `Λ`-modules on `X_proétale` — a sheaf of modules over
the constant coefficient ring sheaf `Λ̲`. If `ℱ` is derived complete along the ideal sheaf `IΛ̲`
cut out by `I`, and `ℱ/Iℱ = 0`, then `ℱ = 0`.

This is the tag's own statement at the tag's own objects. It is
`AlgebraicGeometry.ProEtale.isZero_of_isDerivedComplete_proetale` — the chapter's lemma at the
small pro-étale site for an arbitrary sheaf of rings and an arbitrary sheaf of ideals — read at
`𝒪 = Λ̲` and `ℐ = AlgebraicGeometry.ProEtale.constantCoefficientIdealSheaf`, with that
statement's finite-generation hypothesis discharged by
`AlgebraicGeometry.ProEtale.fg_constantCoefficientIdealSheaf_obj`. The two ringed sites agree
on the nose, so no transport is needed at this step.

`Λ` is an arbitrary commutative ring: `I.FG` is the only hypothesis on the coefficients, as in
the source. The hypothesis `hIF` says the first ideal power product is everything, which is the
vanishing of the adic quotient `ℱ/Iℱ`. -/
@[stacks 09BY]
theorem isZero_of_isDerivedComplete_constantCoefficients (X : Scheme.{u}) (Λ : Type u)
    [CommRing Λ] (I : Ideal Λ) (hI : I.FG)
    (F : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (constantCoefficientRingedSite.{u, u, u} X Λ).O))
    (hF : RingedSite.IsDerivedComplete.{u + 1, u, u + 1, u + 1}
      (constantCoefficientRingedSite.{u, u, u} X Λ)
      (constantCoefficientIdealSheaf.{u, u, u} X Λ I)
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (constantCoefficientRingedSite.{u, u, u} X Λ).O)) 0).obj F))
    (hIF : RingedSite.idealPowerProduct (constantCoefficientRingedSite.{u, u, u} X Λ)
      (constantCoefficientIdealSheaf.{u, u, u} X Λ I) F 1 = ⊤) :
    IsZero F :=
  isZero_of_isDerivedComplete_proetale X
    ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1} Λ)))
    (constantCoefficientIdealSheaf.{u, u, u} X Λ I)
    (fun W _ _ => fg_constantCoefficientIdealSheaf_obj X Λ I hI W) F hF hIF

end AlgebraicGeometry.ProEtale

end
