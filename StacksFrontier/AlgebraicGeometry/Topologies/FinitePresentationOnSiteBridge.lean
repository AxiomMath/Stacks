module

public import Mathlib.Algebra.Category.Grp.Ulift
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Module.ULift
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FinitePresentation

/-!
# Finite presentation on a site, in the two renderings of Stacks 03DL(7)

Stacks 03DL(7) says that a sheaf of modules is of finite presentation when every object of the
site has a covering on whose members the module admits a finite global presentation.  There are
two renderings of this in the library, and they are not the same statement about the same
constant.

`SheafOfModules.IsFinitePresentationOnSite` states it with coproducts and cokernels given by
their universal properties, so it needs no sheafification instances and therefore applies to
the fibred categories of Stacks 06WG.  Mathlib's `SheafOfModules.IsFinitePresentation` states it
with sheafified free modules, so it needs sheafification on every slice, and it is the predicate
that the results on modules on sites — Stacks 0GN0 and 0GMZ among them — are stated for.

This file connects the first to the second.  The content is the passage from a finite global
presentation expressed by universal properties to one expressed by free modules: a coproduct of
copies of the structure sheaf, presented as a colimit cofan, is identified with the sheafified
free module on the same index type, and the cokernel property is transported across that
identification.

## Main results

* `AlgebraicGeometry.SheafOfModules.exists_isFinite_presentation_of_hasFiniteGlobalPresentation`:
  a finite global presentation in the universal-property sense yields a finite
  `SheafOfModules.Presentation`.
* `AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite`: the
  implication between the two renderings of Stacks 03DL(7).

## Implementation notes

Both results are stated with the coefficient rings and the module sections in the universe
`max u v` of the site.  That is forced, not chosen: Mathlib's `SheafOfModules.free` takes an
index type in the module universe, while the index types of a `HasGlobalPresentation` are bounded
by `max u v r m`, so the two agree exactly when the ring and module universes are `max u v`.  At
the associated site of a category fibred in groupoids over the schemes over `S` this is the
universe `u + 1`.

`SheafOfModules.uliftForPresentation` appears in `HasFiniteGlobalPresentation` to put the module
and the ring sheaf in a common universe.  At these universes that lift is the identity up to
isomorphism, which is what `AlgebraicGeometry.SheafOfModules.uliftSelfIso` below records; it is
stated here rather than imported because the corresponding declaration of
`QuasicoherentInternalHom` is private to that file.

No tag is placed.  Stacks 03DL(7) is already carried by
`SheafOfModules.IsFinitePresentationOnSite`, and the results here are the comparison of two
renderings of it rather than a further part of the source's content.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{max u v}}

/-- A colimit cofan over a constant diagram stays a colimit cofan when the constant is replaced
by an isomorphic object, the index type by an equivalent one, and each injection is reindexed
and precomposed with the inverse isomorphism. -/
public def cofanIsColimitOfConstIso {D : Type*} [Category D] {β γ : Type*} {A A' P : D}
    (e : A ≅ A') (q : γ ≃ β) (inj : ∀ _ : β, A ⟶ P)
    (hc : IsColimit (Cofan.mk (f := fun _ : β => A) P inj)) :
    IsColimit (Cofan.mk (f := fun _ : γ => A') P (fun i => e.inv ≫ inj (q i))) :=
  Cofan.IsColimit.mk _
    (fun t => Cofan.IsColimit.desc hc (fun i => e.hom ≫ t.inj (q.symm i)))
    (fun t j => by
      simp only [cofan_mk_inj, Category.assoc]
      rw [show inj (q j) ≫ Cofan.IsColimit.desc hc (fun i => e.hom ≫ t.inj (q.symm i)) =
          e.hom ≫ t.inj (q.symm (q j)) from Cofan.IsColimit.fac hc _ (q j),
        q.symm_apply_apply, ← Category.assoc, e.inv_hom_id, Category.id_comp])
    (fun t m hm => by
      refine Cofan.IsColimit.hom_ext hc m _ (fun j => ?_)
      rw [Cofan.IsColimit.fac]
      have h1 := hm (q.symm j)
      simp only [cofan_mk_inj, Category.assoc, q.apply_symm_apply] at h1
      change inj j ≫ m = e.hom ≫ t.inj (q.symm j)
      rw [← h1, ← Category.assoc, e.hom_inv_id, Category.id_comp])

/-- A finite global presentation in the universal-property sense of Stacks 03DE(7) yields a
finite `SheafOfModules.Presentation`: the two presenting coproducts are identified with the
sheafified free modules on their index types, and the cokernel property is carried across.
Finiteness is immediate, the index types being lifts of the `Fin n` the global presentation
supplies. -/
public theorem exists_isFinite_presentation_of_hasFiniteGlobalPresentation
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (N : _root_.SheafOfModules.{max u v} R) (h : N.HasFiniteGlobalPresentation) :
    ∃ p : N.Presentation, p.IsFinite := by
  classical
  let : HasSheafify J AddCommGrpCat.{max u v} := hasSheafify_of_locallyBijective
  obtain ⟨n, k, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hcok⟩⟩ := h
  let eU := AlgebraicGeometry.SheafOfModules.uliftSelfIso (R := R) (_root_.SheafOfModules.unit R)
  let eN := AlgebraicGeometry.SheafOfModules.uliftSelfIso N
  let eP : _root_.SheafOfModules.free (ULift.{max u v} (Fin n)) ≅ P :=
    (_root_.SheafOfModules.isColimitFreeCofan
      (ULift.{max u v} (Fin n))).coconePointUniqueUpToIso
      (cofanIsColimitOfConstIso eU Equiv.ulift ι hP)
  let eQ : _root_.SheafOfModules.free (ULift.{max u v} (Fin k)) ≅ Q :=
    (_root_.SheafOfModules.isColimitFreeCofan
      (ULift.{max u v} (Fin k))).coconePointUniqueUpToIso
      (cofanIsColimitOfConstIso eU Equiv.ulift κ hQ)
  let f := eQ.hom ≫ a ≫ eP.inv
  let g := eP.hom ≫ b ≫ eN.hom
  have hab' : a ≫ b ≫ eN.hom = 0 := by rw [← Category.assoc, hab, zero_comp]
  have H : f ≫ g = 0 := by
    simp only [f, g, Category.assoc, Iso.inv_hom_id_assoc, hab', comp_zero]
  -- a map out of the free module killing `f` kills `a` after transport, so `b` descends it
  have key : ∀ {Z' : _root_.SheafOfModules.{max u v} R}
      (g' : _root_.SheafOfModules.free (ULift.{max u v} (Fin n)) ⟶ Z'),
      f ≫ g' = 0 → a ≫ (eP.inv ≫ g') = 0 := by
    intro Z' g' eq'
    refine (cancel_epi eQ.hom).mp ?_
    rw [comp_zero]
    simpa only [f, Category.assoc] using eq'
  let dsc : ∀ {Z' : _root_.SheafOfModules.{max u v} R}
      (g' : _root_.SheafOfModules.free (ULift.{max u v} (Fin n)) ⟶ Z'),
      f ≫ g' = 0 → (N ⟶ Z') := fun {_} g' eq' =>
    eN.inv ≫ (CokernelCofork.IsColimit.desc' hcok (eP.inv ≫ g') (key g' eq')).1
  have hb : ∀ {Z' : _root_.SheafOfModules.{max u v} R}
      (g' : _root_.SheafOfModules.free (ULift.{max u v} (Fin n)) ⟶ Z')
      (eq' : f ≫ g' = 0),
      b ≫ (CokernelCofork.IsColimit.desc' hcok (eP.inv ≫ g') (key g' eq')).1 = eP.inv ≫ g' :=
    fun g' eq' => (CokernelCofork.IsColimit.desc' hcok (eP.inv ≫ g') (key g' eq')).2
  have H' : IsColimit (CokernelCofork.ofπ g H) := by
    refine CokernelCofork.IsColimit.ofπ _ _ dsc (fun {Z'} g' eq' => ?_)
      (fun {Z'} g' eq' m hm => ?_)
    · simp only [dsc, g, Category.assoc, Iso.hom_inv_id_assoc, hb g' eq']
    · refine (cancel_epi eN.hom).mp ?_
      simp only [dsc, Iso.hom_inv_id_assoc]
      refine Cofork.IsColimit.hom_ext hcok ?_
      simp only [CokernelCofork.π_ofπ, hb g' eq']
      refine (cancel_epi eP.hom).mp ?_
      rw [Iso.hom_inv_id_assoc]
      simpa only [g, Category.assoc] using hm
  exact ⟨_root_.SheafOfModules.presentationOfIsCokernelFree f g H H',
    ⟨⟨Finite.of_equiv (Fin n) Equiv.ulift.symm⟩,
      ⟨Finite.of_equiv (Fin k) Equiv.ulift.symm⟩⟩⟩

/-- **The two renderings of Stacks 03DL(7) compared.** A sheaf of modules of finite presentation
in the covering-family sense of `SheafOfModules.IsFinitePresentationOnSite` is of finite
presentation in Mathlib's sense.

The covering family required by Stacks 03DN is the family of all objects on which the module
admits a finite global presentation: it covers the final object because, by hypothesis, each
object of the site is covered by such objects. -/
public theorem isFinitePresentation_of_isFinitePresentationOnSite
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (M : _root_.SheafOfModules.{max u v} R) [M.IsFinitePresentationOnSite] :
    M.IsFinitePresentation := by
  rw [Stacks.SheafOfModules.isFinitePresentation_iff_exists_cover_finite_presentations]
  refine ⟨{U : C // (M.over U).HasFiniteGlobalPresentation}, Subtype.val, fun U => ?_,
    fun i => exists_isFinite_presentation_of_hasFiniteGlobalPresentation (M.over i.val) i.property⟩
  obtain ⟨I, V, f, hf, hV⟩ :=
    _root_.SheafOfModules.IsFinitePresentationOnSite.locally_hasFiniteGlobalPresentation (F := M) U
  refine J.superset_covering ((Sieve.generate_le_iff _ _).mpr ?_) hf
  rintro _ _ ⟨i⟩
  exact ⟨⟨V i, hV i⟩, ⟨𝟙 _⟩⟩

end SheafOfModules

end AlgebraicGeometry

end
