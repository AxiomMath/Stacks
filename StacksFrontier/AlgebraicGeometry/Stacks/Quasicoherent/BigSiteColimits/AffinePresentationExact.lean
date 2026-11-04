module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.PresheafCokernel

/-!
# Surjectivity on sections of the presenting morphism of a global presentation

A global presentation exhibits a sheaf of modules as a cokernel *in sheaves of modules* of a map
between coproducts of copies of the structure sheaf.  The sections of a cokernel in sheaves are
not the cokernel of the sections, so surjectivity of the presenting morphism on the sections over
an object is not part of the data of a presentation; it is the one hypothesis of the cokernel step
which has to be proved, and over an affine object of a big site of schemes it is the vanishing of
the first cohomology of a quasi-coherent module on an affine, Stacks 03DW.

This file isolates the two statements which reduce that surjectivity to the sheaf condition for
the cokernel computed in *presheaves*, and does so in a form which never asks for the sheaf
condition away from the object where surjectivity is wanted and the fibre products of one covering
family of it.

The first reduction is formal.  If the cokernel of the same map taken in presheaves of modules
happens to be a sheaf, then it is also the cokernel in sheaves of modules, because the forgetful
functor from sheaves to presheaves is fully faithful; two cokernels of one morphism agree up to a
unique isomorphism compatible with the projections, and the projection onto a presheaf cokernel is
surjective on the sections over every object by construction.  So the presenting morphism is
surjective on sections everywhere.

The second reduction is where the content is, and it is a statement about one object.  The
comparison from the presheaf cokernel to the sheaf cokernel is locally surjective and locally
injective, being a sheafification; so a section of the sheaf cokernel over an object lifts to the
presheaf cokernel over the members of some covering family, and two such lifts agree only locally
over a fibre product of two members.  Local agreement is upgraded to agreement by injectivity of
the comparison over that fibre product, after which the lifts are a compatible family and the
sheaf condition for the covering family amalgamates them.  Nothing is asked of the presheaf
cokernel at any other object: in particular the sheaf condition at the objects which are not
members of the family, or not fibre products of two members, plays no part.  This is what makes
the reduction usable on a slice of a big fppf site, where the family may be taken to consist of
affine objects and the fibre product of two affine objects over an affine object is again affine,
so that the Amitsur complex computes everything that is needed.

## Main results

* `CategoryTheory.Presheaf.injective_app_of_isSeparatedFor`: **a locally injective morphism of
  presheaves is injective on the sections over an object for which the source is separated.**
* `CategoryTheory.Presheaf.exists_app_eq_of_isSheafFor_arrows`: **a section of the target which
  lifts over the members of a covering family is a value of the morphism**, provided the source
  satisfies the sheaf condition for that family, the target is separated for it, and the morphism
  is injective on the sections over the pairwise fibre products of the family.
* `CategoryTheory.Presheaf.surjective_app_of_forall_exists_isSheafFor_arrows`: the two combined —
  **surjectivity over an object from one covering family per section**, with the sheaf condition
  demanded at the object alone and separatedness at the pairwise fibre products alone.
* `SheafOfModules.surjective_val_app_of_isSheaf_cokernel`: **the presenting morphism of a
  presentation whose cokernel of presheaves is a sheaf is surjective on the sections over every
  object.**

## Implementation notes

The two site-level results are stated for presheaves of types, which is the generality in which
`CategoryTheory.Presieve.IsSheafFor` is phrased; a consumer holding presheaves of modules composes
with `CategoryTheory.forget`, as in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.PresheafCokernel`.

Local injectivity is taken as the plain statement that two sections identified by the morphism
agree along the arrows of some covering sieve, rather than through
`CategoryTheory.Presheaf.IsLocallyInjective`, so that no concreteness of the target category is
involved and a caller may supply it for a composite with a forgetful functor.

`SheafOfModules.surjective_val_app_of_isSheaf_cokernel` is stated for the categorical cokernel of
presheaves of modules rather than for an arbitrary morphism with the property of
`PresheafOfModules.IsPresheafCokernel`, because the morphism to the sheaf cokernel is produced by
the universal property and not by the property.

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w' w u v r m

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] {F G : Cᵒᵖ ⥤ Type w} (θ : F ⟶ G)

/-- **A locally injective morphism of presheaves is injective on the sections over an object for
which the source is separated.**  Two sections identified by the morphism agree along the arrows
of a covering sieve, and separatedness for that sieve makes them equal.

Local injectivity is phrased as the existence of such a sieve rather than through
`CategoryTheory.Presheaf.IsLocallyInjective`, which it is for the sieve
`CategoryTheory.Presheaf.equalizerSieve`. -/
theorem injective_app_of_isSeparatedFor (J : GrothendieckTopology C) (Z : C)
    (hloc : ∀ x y : F.obj (op Z), θ.app (op Z) x = θ.app (op Z) y →
      ∃ S : Sieve Z, S ∈ J Z ∧ ∀ ⦃V : C⦄ (f : V ⟶ Z), S f → F.map f.op x = F.map f.op y)
    (hsep : ∀ S : Sieve Z, S ∈ J Z → Presieve.IsSeparatedFor F (S : Presieve Z)) :
    Function.Injective (θ.app (op Z)) := fun x y hxy => by
  obtain ⟨S, hS, h⟩ := hloc x y hxy
  exact (hsep S hS).ext fun {_} {f} hf => h f hf

/-- **A section of the target which lifts over the members of a covering family is a value of the
morphism.**  The lifts agree on the pairwise fibre products of the family, because the morphism
carries both of their restrictions to the restriction of the given section and is injective on the
sections there; so they form a compatible family, which the sheaf condition for the family
amalgamates; and the value of the morphism on the amalgamation agrees with the given section along
the family, hence equals it by separatedness of the target.

Only the object `W`, the members of the family and their pairwise fibre products enter: the sheaf
condition for the source is used at `W` for this one family, and separatedness of the source
nowhere at all. -/
theorem exists_app_eq_of_isSheafFor_arrows {W : C} {I : Type w'} {Y : I → C} (g : ∀ i, Y i ⟶ W)
    [(Presieve.ofArrows Y g).HasPairwisePullbacks]
    (hF : Presieve.IsSheafFor F (Presieve.ofArrows Y g))
    (hG : Presieve.IsSeparatedFor G (Presieve.ofArrows Y g))
    (hinj : ∀ i j, Function.Injective (θ.app (op (pullback (g i) (g j)))))
    {n : G.obj (op W)}
    (hn : ∀ i, ∃ s : F.obj (op (Y i)), θ.app (op (Y i)) s = G.map (g i).op n) :
    ∃ t : F.obj (op W), θ.app (op W) t = n := by
  choose s hs using hn
  rw [Presieve.isSheafFor_arrows_iff_pullbacks] at hF
  obtain ⟨t, ht, -⟩ := hF s fun i j => hinj i j (by
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hs, hs,
      ← Functor.map_comp_apply, ← Functor.map_comp_apply,
      ← op_comp, ← op_comp, pullback.condition])
  refine ⟨t, hG.ext fun {Z} {f} hf => ?_⟩
  obtain ⟨i⟩ := hf
  rw [← NatTrans.naturality_apply, ht i, hs i]

/-- **Surjectivity over an object from one covering family per section.**  For each section of the
target over `W` a covering family of `W` is required, with the sheaf condition for the source and
separatedness for the target on it, separatedness for the source over its pairwise fibre products,
and a lift of the section over each member.  Then the morphism is surjective on the sections over
`W`.

The two reductions of the file combined: `CategoryTheory.Presheaf.injective_app_of_isSeparatedFor`
turns separatedness over a fibre product into injectivity there, and
`CategoryTheory.Presheaf.exists_app_eq_of_isSheafFor_arrows` glues.  What a caller has to know
about the source is therefore confined to `W`, to the members of the family and to the pairwise
fibre products of the family; the sheaf condition at every other object of the site is not used,
and neither is separatedness of the source at `W` itself. -/
theorem surjective_app_of_forall_exists_isSheafFor_arrows (J : GrothendieckTopology C) {W : C}
    (hloc : ∀ (Z : C) (x y : F.obj (op Z)), θ.app (op Z) x = θ.app (op Z) y →
      ∃ S : Sieve Z, S ∈ J Z ∧ ∀ ⦃V : C⦄ (f : V ⟶ Z), S f → F.map f.op x = F.map f.op y)
    (h : ∀ n : G.obj (op W), ∃ (I : Type w') (Y : I → C) (g : ∀ i, Y i ⟶ W),
      ∃ _ : (Presieve.ofArrows Y g).HasPairwisePullbacks,
        Presieve.IsSheafFor F (Presieve.ofArrows Y g) ∧
          Presieve.IsSeparatedFor G (Presieve.ofArrows Y g) ∧
          (∀ (i j : I) (S : Sieve (pullback (g i) (g j))), S ∈ J (pullback (g i) (g j)) →
            Presieve.IsSeparatedFor F (S : Presieve (pullback (g i) (g j)))) ∧
          ∀ i, ∃ s : F.obj (op (Y i)), θ.app (op (Y i)) s = G.map (g i).op n) :
    Function.Surjective (θ.app (op W)) := fun n => by
  obtain ⟨I, Y, g, hpb, hF, hG, hsep, hn⟩ := h n
  exact exists_app_eq_of_isSheafFor_arrows θ g hF hG
    (fun i j => injective_app_of_isSeparatedFor θ J _ (hloc _) (hsep i j)) hn

end CategoryTheory.Presheaf

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- **The presenting morphism of a presentation whose cokernel of presheaves is a sheaf is
surjective on the sections over every object.**

Let `b : P ⟶ N` be a cokernel of `a : Q ⟶ P` in sheaves of modules and suppose the cokernel of
`a.val` taken in presheaves of modules is a sheaf.  Then that presheaf cokernel, viewed as a sheaf
of modules, is a cokernel of `a` in sheaves of modules as well — a morphism out of it to a sheaf of
modules is a morphism of presheaves of modules, the forgetful functor being fully faithful — so the
two projections differ by an isomorphism, and the projection onto a cokernel of presheaves is
surjective on the sections over every object.

This is the formal half of the cokernel step of a global presentation: the surjectivity which
`SheafOfModules.globalSectionSpan_eq_top_of_surjective_val_app` and
`SheafOfModules.exists_baseChangeEquiv_of_exact_sections` ask for, reduced to the sheaf condition
for the cokernel of presheaves, whose sections are computed by
`SheafOfModules.exists_baseChangeEquiv_of_isPresheafCokernel`. -/
theorem surjective_val_app_of_isSheaf_cokernel {Q P N : SheafOfModules.{m} R}
    (a : Q ⟶ P) (b : P ⟶ N) (hab : a ≫ b = 0)
    (hN : IsColimit (CokernelCofork.ofπ b hab))
    (hsheaf : Presheaf.IsSheaf J (cokernel a.val).presheaf) (X : Cᵒᵖ) :
    Function.Surjective (b.val.app X) := by
  have hzero : ∀ {Y Z : SheafOfModules.{m} R}, (0 : Y ⟶ Z).val = 0 := rfl
  have hab' : a.val ≫ b.val = 0 := by rw [← comp_val, hab, hzero]
  let N' : SheafOfModules.{m} R := ⟨cokernel a.val, hsheaf⟩
  let π : P ⟶ N' := ⟨cokernel.π a.val⟩
  have hπ : a ≫ π = 0 := SheafOfModules.hom_ext (by
    change a.val ≫ cokernel.π a.val = _
    rw [cokernel.condition, hzero])
  let θ : N' ⟶ N := ⟨cokernel.desc a.val b.val hab'⟩
  have hθval : cokernel.π a.val ≫ θ.val = b.val := cokernel.π_desc a.val b.val hab'
  have hθ : π ≫ θ = b := SheafOfModules.hom_ext hθval
  obtain ⟨σ, hσ⟩ := CokernelCofork.IsColimit.desc' hN π hπ
  have hσ' : b ≫ σ = π := hσ
  have hid : σ ≫ θ = 𝟙 N := Cofork.IsColimit.hom_ext hN (by
    change b ≫ σ ≫ θ = b ≫ 𝟙 N
    rw [← Category.assoc, hσ', hθ, Category.comp_id])
  have hidval : σ.val ≫ θ.val = 𝟙 N.val := by rw [← comp_val, hid, id_val]
  intro n
  obtain ⟨p, hp⟩ := PresheafOfModules.surjective_of_epi (cokernel.π a.val) X (σ.val.app X n)
  refine ⟨p, ?_⟩
  have h1 : (cokernel.π a.val ≫ θ.val).app X p = b.val.app X p := by rw [hθval]
  rw [← h1, PresheafOfModules.comp_app]
  change θ.val.app X ((cokernel.π a.val).app X p) = n
  rw [hp]
  have h2 : (σ.val ≫ θ.val).app X n = (𝟙 N.val : N.val ⟶ N.val).app X n := by rw [hidval]
  rw [PresheafOfModules.comp_app] at h2
  exact h2.trans (by simp)

end SheafOfModules

end
