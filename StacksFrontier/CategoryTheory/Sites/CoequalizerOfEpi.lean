module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.RegularEpi
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A sheaf of sets is the coequalizer of any epimorphism onto its kernel pair

Let `p : G ⟶ F` be an epimorphism of sheaves of sets on a site. Epimorphisms of type-valued
sheaves are regular, hence effective, so `F` is the coequalizer of the kernel pair of `p`. If
moreover `q : H ⟶ R` is an epimorphism onto the vertex of that kernel pair, then `F` is already
the coequalizer of `q ≫ R.fst` and `q ≫ R.snd`: precomposing a coequalizer cofork with an
epimorphism leaves it a coequalizer.

This is the purely categorical step with which the Stacks Project proves that a presentation of
a sheaf of sets by a coequalizer exists as soon as two surjections do — a surjection
`G ⟶ F` and then a surjection `H` onto `G ×_F G`. It is stated for an arbitrary kernel-pair
cone rather than for a chosen `pullback p p`, because the consumer has a cone whose vertex is
built from the geometry and should not have to identify it with the chosen pullback.

## Main results

* `CategoryTheory.Sheaf.isColimitCoforkOfEpiOfEpi` — the cofork on `p` over the pair
  `(q ≫ c.fst, q ≫ c.snd)` is a colimit.
* `CategoryTheory.Sheaf.nonempty_coequalizer_iso_of_epi_of_epi` — its consequence in the form a
  coequalizer presentation is usually stated in, an isomorphism from the chosen coequalizer.
* `CategoryTheory.Sheaf.epi_presheafToSheaf_map` — a locally surjective morphism of presheaves of
  sets sheafifies to an epimorphism.
* `CategoryTheory.Sheaf.isColimitCoforkOfLocallySurjective` — the same coequalizer presentation
  read off two *locally surjective* maps of presheaves, which is the form the geometry supplies
  it in: a locally surjective `A ⟶ T` with `T` terminal, and a locally surjective map onto
  `A ×_T A`.

## Implementation notes

That every epimorphism of type-valued sheaves is regular is
`CategoryTheory.isRegularEpiCategory_sheaf`, which needs sheafification for the coefficient
category and is therefore carried here as the hypothesis `HasSheafify J (Type w)`; it is not
available for a general coefficient category, which is why these statements are about sheaves of
sets. `CategoryTheory.IsRegularEpiCategory.regularEpiOfEpi` is a field rather than an instance,
so it is introduced by hand before `CategoryTheory.Limits.EffectiveEpi` can be synthesized.

`CategoryTheory.Sheaf.isColimitCoforkOfEpiOfEpi` produces colimit data, so it is a `def`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasSheafify J (Type w)]
  {F G H : Sheaf J (Type w)}

/-- **An epimorphism of sheaves of sets exhibits its target as a coequalizer, and the kernel pair
may be replaced by anything mapping onto it epimorphically.** Here `c` is a kernel pair of the
epimorphism `p : G ⟶ F` and `q : H ⟶ c.pt` is an epimorphism onto its vertex. -/
public def isColimitCoforkOfEpiOfEpi
    (p : G ⟶ F) [Epi p] (c : PullbackCone p p) (hc : IsLimit c)
    (q : H ⟶ c.pt) [Epi q] :
    IsColimit (Cofork.ofπ p (show (q ≫ c.fst) ≫ p = (q ≫ c.snd) ≫ p by
      simp only [Category.assoc, c.condition])) := by
  have := IsRegularEpiCategory.regularEpiOfEpi p
  exact isCoequalizerEpiComp (isColimitCoforkOfEffectiveEpi p c hc) q

/-- **The coequalizer presentation given by two epimorphisms.** The target of an epimorphism of
sheaves of sets is isomorphic to the coequalizer of the two composites of an epimorphism onto its
kernel pair with the two projections. -/
public theorem nonempty_coequalizer_iso_of_epi_of_epi
    (p : G ⟶ F) [Epi p] (c : PullbackCone p p) (hc : IsLimit c)
    (q : H ⟶ c.pt) [Epi q] [HasCoequalizer (q ≫ c.fst) (q ≫ c.snd)] :
    Nonempty (coequalizer (q ≫ c.fst) (q ≫ c.snd) ≅ F) :=
  ⟨IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (isColimitCoforkOfEpiOfEpi p c hc q)⟩

section LocallySurjective

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- A locally surjective morphism of presheaves of sets becomes an epimorphism of sheaves after
sheafification. -/
@[sga "4 II 5.1" "partial"]
public theorem epi_presheafToSheaf_map {F G : Cᵒᵖ ⥤ Type u} (f : F ⟶ G)
    [Presheaf.IsLocallySurjective J f] :
    Epi ((presheafToSheaf J (Type u)).map f) := by
  have : Presheaf.IsLocallySurjective J (f ≫ toSheafify J G) := inferInstance
  have : Presheaf.IsLocallySurjective J (sheafifyMap J f) :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J (toSheafify_naturality J f).symm
  exact (Sheaf.isLocallySurjective_iff_epi ((presheafToSheaf J (Type u)).map f)).1 this

/-- **A sheaf of sets is the coequalizer of two locally surjective presheaf maps.** Let
`aug : A ⟶ T` be a locally surjective morphism of presheaves of sets with `T` terminal, and let
`m : B ⟶ A ×_T A` be locally surjective too. Then after sheafification `B ⇉ A ⟶ ⊤` is a
coequalizer.

`aug` sheafifies to an epimorphism onto the terminal sheaf, whose kernel pair is the
sheafification of `A ×_T A` because sheafification is left exact, and `m` sheafifies to an
epimorphism onto that kernel pair; so `isColimitCoforkOfEpiOfEpi` applies. -/
public noncomputable def isColimitCoforkOfLocallySurjective
    {A B T : Cᵒᵖ ⥤ Type u} (aug : A ⟶ T) (hT : IsTerminal T)
    [Presheaf.IsLocallySurjective J aug]
    (m : B ⟶ pullback aug aug) [Presheaf.IsLocallySurjective J m] :
    IsColimit (Cofork.ofπ (terminal.from ((presheafToSheaf J (Type u)).obj A))
      (show (presheafToSheaf J (Type u)).map (m ≫ pullback.fst aug aug) ≫
            terminal.from ((presheafToSheaf J (Type u)).obj A) =
          (presheafToSheaf J (Type u)).map (m ≫ pullback.snd aug aug) ≫
            terminal.from ((presheafToSheaf J (Type u)).obj A)
        from terminal.hom_ext _ _)) := by
  have : Epi ((presheafToSheaf J (Type u)).map aug) := epi_presheafToSheaf_map J aug
  have hTs : IsTerminal ((presheafToSheaf J (Type u)).obj T) :=
    hT.isTerminalObj (presheafToSheaf J (Type u)) T
  have : Epi (terminal.from ((presheafToSheaf J (Type u)).obj A)) := by
    rw [show terminal.from ((presheafToSheaf J (Type u)).obj A) =
        (presheafToSheaf J (Type u)).map aug ≫
          (hTs.uniqueUpToIso (terminalIsTerminal (C := Sheaf J (Type u)))).hom from
      terminal.hom_ext _ _]
    infer_instance
  have hpb : IsPullback
      ((presheafToSheaf J (Type u)).map (pullback.fst aug aug))
      ((presheafToSheaf J (Type u)).map (pullback.snd aug aug))
      ((presheafToSheaf J (Type u)).map aug) ((presheafToSheaf J (Type u)).map aug) :=
    IsPullback.of_isLimit (isLimitPullbackConeMapOfIsLimit
      (presheafToSheaf J (Type u)) _ (pullbackIsPullback _ _))
  have hpb2 : IsPullback
      ((presheafToSheaf J (Type u)).map (pullback.fst aug aug))
      ((presheafToSheaf J (Type u)).map (pullback.snd aug aug))
      (terminal.from ((presheafToSheaf J (Type u)).obj A))
      (terminal.from ((presheafToSheaf J (Type u)).obj A)) :=
    hpb.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (hTs.uniqueUpToIso (terminalIsTerminal (C := Sheaf J (Type u))))
      (by rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp])
      (by rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp])
      (terminal.hom_ext _ _) (terminal.hom_ext _ _)
  have : Epi ((presheafToSheaf J (Type u)).map m) := epi_presheafToSheaf_map J m
  have hlim : IsLimit (PullbackCone.mk
      ((presheafToSheaf J (Type u)).map (pullback.fst aug aug))
      ((presheafToSheaf J (Type u)).map (pullback.snd aug aug)) hpb2.w) := hpb2.isLimit
  have hcof := @Sheaf.isColimitCoforkOfEpiOfEpi _ _ _ _ _ _ _
    (terminal.from ((presheafToSheaf J (Type u)).obj A)) inferInstance _ hlim
    ((presheafToSheaf J (Type u)).map m) (epi_presheafToSheaf_map J m)
  refine Cofork.isColimitOfIsos _ hcof _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · simp only [PullbackCone.mk_fst, Iso.refl_hom, Category.id_comp, Category.comp_id,
      Functor.map_comp]
  · simp only [PullbackCone.mk_snd, Iso.refl_hom, Category.id_comp, Category.comp_id,
      Functor.map_comp]
  · exact terminal.hom_ext _ _

end LocallySurjective

end CategoryTheory.Sheaf

end
