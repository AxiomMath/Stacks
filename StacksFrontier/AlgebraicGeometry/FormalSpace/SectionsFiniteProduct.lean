module

public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.FppfCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Sections of a sheaf over the spectrum of a finite product of rings

The spectrum of a finite product `Π i, T i` of rings is the disjoint union of the spectra
`Spec (T i)`: the projections `Spec (T i) ⟶ Spec (Π i, T i)` are open immersions with pairwise
disjoint, jointly covering images. So for a sheaf `F` on the big fppf site of `S`, a section of `F`
over an object of the site whose scheme is `Spec (Π i, T i)` is the same thing as a family of
sections over objects whose schemes are the `Spec (T i)`.

This is the form in which the theorems on morphisms into an algebraic space over a complete local
ring extend to finite products of complete local rings, such as the tensor product `R' ⊗_R R'` of
a finite étale extension of a Noetherian complete local ring `R` with itself.

## Main results

* `AlgebraicGeometry.BigFppfOver.existsUnique_section_of_pi`: sections over the spectrum of a
  finite product are families of sections over the spectra of the factors.

## Implementation notes

The compatibility condition of the sheaf property is vacuous: two factors with distinct indices
have disjoint images, so an object of the site mapping to both has an empty scheme, and over such
an object the empty sieve covers, so the sheaf has at most one section there.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.BigFppfOver

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A sheaf on the big fppf site has at most one section over an object with empty scheme. -/
theorem subsingleton_of_isEmpty {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (hF : Presheaf.IsSheaf (topology B S hS) F) (Z : BigFppfOver B S hS)
    (hZ : IsEmpty ((toScheme B S hS).obj Z)) : Subsingleton (F.obj (op Z)) :=
  ⟨fun _ _ => (((isSheaf_iff_isSheaf_of_type (topology B S hS) F).1 hF) _
    (bot_mem_topology Z hZ)).isSeparatedFor.ext fun _ _ h => h.elim⟩

/-- The projection from the spectrum of a finite product onto the spectrum of a factor is an open
immersion. -/
theorem isOpenImmersion_specMap_evalRingHom {ι : Type u} [Finite ι] (T : ι → Type u)
    [∀ i, CommRing (T i)] (i : ι) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (Pi.evalRingHom T i))) := by
  rw [← ι_sigmaSpec (fun i => CommRingCat.of (T i)) i]
  have : IsOpenImmersion (Sigma.ι (fun i => Spec (CommRingCat.of (T i))) i) :=
    (sigmaOpenCover (fun i => Spec (CommRingCat.of (T i)))).map_prop i
  infer_instance

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **Sections over the spectrum of a finite product.** Let `U` be an object of the big fppf site
of `S` whose scheme is identified with `Spec (Π i, T i)` for a finite family of rings, and let
`j i : U i ⟶ U` be morphisms of the site which, read through identifications of the schemes of
the `U i` with the `Spec (T i)`, are the projections. Then for a sheaf `F`, every family of
sections `x i` over the `U i` is the family of restrictions of a unique section over `U`. -/
theorem existsUnique_section_of_pi {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (hF : Presheaf.IsSheaf (topology B S hS) F)
    {ι : Type u} [Finite ι] (T : ι → Type u) [∀ i, CommRing (T i)]
    (U : BigFppfOver B S hS) (eU : (toScheme B S hS).obj U ≅ Spec (.of (Π i, T i)))
    (Ui : ι → BigFppfOver B S hS) (eUi : ∀ i, (toScheme B S hS).obj (Ui i) ≅ Spec (.of (T i)))
    (j : ∀ i, Ui i ⟶ U)
    (hj : ∀ i, (toScheme B S hS).map (j i) ≫ eU.hom =
      (eUi i).hom ≫ Spec.map (CommRingCat.ofHom (Pi.evalRingHom T i)))
    (x : ∀ i, F.obj (op (Ui i))) :
    ∃! y : F.obj (op U), ∀ i, F.map (j i).op y = x i := by
  classical
  let R : ι → CommRingCat.{u} := fun i => CommRingCat.of (T i)
  have hopen : ∀ i, IsOpenImmersion ((toScheme B S hS).map (j i)) := fun i => by
    rw [(Iso.eq_comp_inv eU).2 (hj i)]
    have := isOpenImmersion_specMap_evalRingHom T i
    infer_instance
  have hsurj : ∀ z : (toScheme B S hS).obj U, ∃ (i : ι) (y : (toScheme B S hS).obj (Ui i)),
      ((toScheme B S hS).map (j i)).base y = z := by
    intro z
    obtain ⟨w, hw⟩ : ∃ w, (sigmaSpec R).base w = eU.hom.base z :=
      ⟨(inv (sigmaSpec R)).base (eU.hom.base z), by
        rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
        rfl⟩
    obtain ⟨⟨i, w'⟩, rfl⟩ := (sigmaMk (fun i => Spec (R i))).surjective w
    refine ⟨i, (eUi i).inv.base w', ?_⟩
    rw [sigmaMk_mk, ← Scheme.Hom.comp_apply, ι_sigmaSpec] at hw
    apply eU.hom.homeomorph.injective
    show ((toScheme B S hS).map (j i) ≫ eU.hom).base ((eUi i).inv.base w') = _
    rwa [hj i, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply (eUi i).inv, Iso.inv_hom_id]
  refine (Presieve.isSheafFor_arrows_iff _ _).1 ((Presieve.isSheafFor_iff_generate _).2
    (((isSheaf_iff_isSheaf_of_type (topology B S hS) F).1 hF) _
      (Space.generate_ofArrows_mem_topology_of_openCover B S hS Ui j hopen hsurj))) x
    fun i k Z gi gk hgk => ?_
  by_cases hik : i = k
  · subst hik
    have : Mono (j i) := (toScheme B S hS).mono_of_mono_map inferInstance
    rw [(cancel_mono (j i)).1 hgk]
  · have hZ : IsEmpty ((toScheme B S hS).obj Z) := by
      refine isEmpty_of_commSq_sigmaι_of_ne (g := fun i => Spec (R i))
        (a := (toScheme B S hS).map gi ≫ (eUi i).hom)
        (b := (toScheme B S hS).map gk ≫ (eUi k).hom) ⟨?_⟩ hik
      rw [← cancel_mono (sigmaSpec R)]
      simp only [Category.assoc, ι_sigmaSpec]
      rw [← hj i, ← hj k, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, hgk]
    exact (subsingleton_of_isEmpty hF Z hZ).elim _ _

end AlgebraicGeometry.BigFppfOver

end
