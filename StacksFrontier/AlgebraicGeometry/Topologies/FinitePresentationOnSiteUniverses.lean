module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalPresentationOfPresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackPresentationAssembly
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfPresentation

/-!
# The two renderings of finite presentation of a module on a site, in any module universe

Stacks 03DL(7) calls a sheaf of modules of finite presentation when every object of the site has
a covering on whose members the module is the cokernel of a map between finite coproducts of
copies of the structure sheaf.  There are two renderings of this.
`SheafOfModules.IsFinitePresentationOnSite` writes the coproducts and the cokernel through their
universal properties, after raising the sections of the module into a universe containing the
site; Mathlib's `SheafOfModules.IsFinitePresentation` writes them with sheafified free modules on
the module's own universe, and is the predicate that the results on pullback of modules —
Stacks 03DO among them — are stated for.

The two are compared here **with the module universe arbitrary**: the coefficient rings and the
sections of the module live in one universe `m`, and the universes of the objects and of the
morphisms of the site are unconstrained.  That is the generality the small étale site of an
algebraic space needs, its objects lying one universe above its sections.

The comparison at a single object is the whole content; the passage from it to the two
covering-family conditions is bookkeeping with `CategoryTheory.Sieve.ofObjects`.  Both halves of
the comparison go through the universe lift of the sections *as a functor*: it is full, faithful
and preserves colimits, so it carries the two colimits of a presentation up and — being fully
faithful — reflects them back down.

## Main results

* `SheafOfModules.HasFiniteGlobalPresentation.of_presentation'`: a finite presentation gives a
  finite global presentation in the sense of Stacks 03DE(7).
* `SheafOfModules.exists_isFinite_presentation_of_hasFiniteGlobalPresentation'`: the converse.
* `SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite'`: finite presentation on
  the site implies finite presentation in the sense of Mathlib.
* `Stacks.Sheaves.FinitePresentation.pullbackModules_isFinitePresentationOnSite`: **Stacks 03DO
  for the clause 03DL(7), in the form stated with
  `SheafOfModules.IsFinitePresentationOnSite`.**

## Implementation notes

`SheafOfModules.HasFiniteGlobalPresentation` places its two coproducts in the universe
`max u v r m` obtained from the universes of the site, of the rings and of the sections, and
compares them with the module through `SheafOfModules.uliftForPresentation`.  A Mathlib
`SheafOfModules.Presentation` lives in the module universe `m` on the nose.  When `m` already
contains the site the lift is an isomorphism and the two descriptions are the same diagram; that
is the case treated in
`StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteBridge`, whose
`AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite` is the
statement below under that extra hypothesis.  Here `m` is arbitrary, so the two descriptions sit
in different universes and the lift has to be used as a functor, exactly as
`SheafOfModules.HasGlobalPresentation.of_presentation'` uses it for the infinite case.  Neither
statement is an instance of the other and both are kept.

The index types of a finite global presentation are `Fin n` and `Fin k`, while those of a
Mathlib presentation must lie in the module universe; the two are related by `ULift` and by
`CategoryTheory.Limits.Cofan` reindexing along an equivalence, which carries no content.

Nothing here carries a Stacks attribute: Stacks 03DL(7) is already registered against both
predicates, and Stacks 03DO against the pullback statement for Mathlib's predicate.  What is
added is the comparison of the two renderings and the restatement of Stacks 03DO through it.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v m

namespace SheafOfModules

/-- A colimiting cofan over a constant family stays one after reindexing the index type along an
equivalence. -/
private noncomputable def isColimitCofanOfEquiv {D : Type*} [Category D] {β γ : Type*} {A P : D}
    (q : γ ≃ β) (inj : ∀ _ : β, A ⟶ P)
    (h : IsColimit (Cofan.mk (f := fun _ : β => A) P inj)) :
    IsColimit (Cofan.mk (f := fun _ : γ => A) P fun i => inj (q i)) := by
  refine Cofan.IsColimit.mk _ (fun s => Cofan.IsColimit.desc h fun b => s.inj (q.symm b)) ?_ ?_
  · intro s i
    simpa only [cofan_mk_inj, Equiv.symm_apply_apply] using
      Cofan.IsColimit.fac h (fun b => s.inj (q.symm b)) (q i)
  · intro s n hn
    refine Cofan.IsColimit.hom_ext h _ _ fun b => ?_
    rw [Cofan.IsColimit.fac h (fun b => s.inj (q.symm b)) b]
    simpa only [cofan_mk_inj, Equiv.apply_symm_apply] using hn (q.symm b)

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {S : Sheaf J RingCat.{m}}
  [HasWeakSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- A functor preserving colimits carries the free cofan on `I` to a colimiting cofan, which stays
colimiting after reindexing along an equivalence. -/
private theorem nonempty_isColimit_map_freeCofan_of_equiv {D : Type*} [Category D]
    (U : SheafOfModules.{m} S ⥤ D)
    [PreservesColimitsOfSize.{m, m} U] {γ : Type*} (I : Type m) (q : γ ≃ I) :
    Nonempty (IsColimit (Cofan.mk (f := fun _ : γ => U.obj (unit S)) (U.obj (free I))
      fun i => U.map ((freeCofan I).inj (q i)))) :=
  ⟨isColimitCofanOfEquiv q (fun i => U.map ((freeCofan I).inj i))
    ((Cofan.isColimitMapCoconeEquiv U _ (freeCofan I))
      (isColimitOfPreserves U (isColimitFreeCofan I)))⟩

/-- **A finite global presentation from a finite presentation, in an arbitrary module universe.**
A sheaf of modules presented as the cokernel of a map between free modules on finite index types
is the cokernel of a map between finite coproducts of copies of the structure sheaf, in the sense
of Stacks 03DE(7): the universe lift of the sections carries both colimits to colimits of the
same shape, and the finite index types are reindexed along `ULift`. -/
theorem HasFiniteGlobalPresentation.of_presentation' {M : SheafOfModules.{m} S}
    (p : M.Presentation) (hp : p.IsFinite) : M.HasFiniteGlobalPresentation := by
  have hgen : Finite p.generators.I := hp.isFiniteType_generators.finite
  have hrel : Finite p.relations.I := hp.isFiniteType_relations.finite
  obtain ⟨n, ⟨eg⟩⟩ := Finite.exists_equiv_fin p.generators.I
  obtain ⟨k, ⟨er⟩⟩ := Finite.exists_equiv_fin p.relations.I
  let : HasSheafify J AddCommGrpCat.{m} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let : HasSheafify J AddCommGrpCat.{max u v m} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v m, v, u} J
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max u v m} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v m, u, v} J
  let U := uliftForPresentationFunctor.{u, v, m, m, max u v m} (R := S)
  have hU : PreservesColimitsOfSize.{m, m} U :=
    uliftForPresentationFunctor_preservesColimits.{u, v, m, m, max u v m} (R := S)
  have := hU
  have : PreservesColimitsOfSize.{0, 0} U := preservesColimitsOfSize_shrink U
  have : U.PreservesZeroMorphisms :=
    preservesZeroMorphisms_uliftForPresentationFunctor.{u, v, m, m, max u v m} (R := S)
  have hcok := isColimitCoforkMapOfIsColimit' U _ p.isColimit
  obtain ⟨hP⟩ := nonempty_isColimit_map_freeCofan_of_equiv U p.generators.I eg.symm
  obtain ⟨hQ⟩ := nonempty_isColimit_map_freeCofan_of_equiv U p.relations.I er.symm
  exact ⟨n, k, U.obj (freeCofan p.generators.I).pt, U.obj (freeCofan p.relations.I).pt,
    (fun i => U.map ((freeCofan p.generators.I).inj (eg.symm i))),
    (fun i => U.map ((freeCofan p.relations.I).inj (er.symm i))),
    ⟨hP⟩, ⟨hQ⟩, U.map _, U.map p.generators.π, _, ⟨hcok⟩⟩

/-- **A finite presentation from a finite global presentation, in an arbitrary module universe.**
This is the converse of `SheafOfModules.HasFiniteGlobalPresentation.of_presentation'`.

The universe lift of the sections is full and faithful and preserves colimits, so the two
presenting coproducts of the given finite global presentation are identified with the lifts of
the free modules on the lifted finite index types, the two presenting morphisms come from
morphisms of those free modules, and the cokernel property descends. -/
theorem exists_isFinite_presentation_of_hasFiniteGlobalPresentation'
    {M : SheafOfModules.{m} S} (h : M.HasFiniteGlobalPresentation) :
    ∃ p : M.Presentation, p.IsFinite := by
  obtain ⟨n, k, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hcok⟩⟩ := h
  let : HasSheafify J AddCommGrpCat.{m} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let : HasSheafify J AddCommGrpCat.{max u v m} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v m, v, u} J
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max u v m} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v m, u, v} J
  let U := uliftForPresentationFunctor.{u, v, m, m, max u v m} (R := S)
  have hU : PreservesColimitsOfSize.{m, m} U :=
    uliftForPresentationFunctor_preservesColimits.{u, v, m, m, max u v m} (R := S)
  have := hU
  have : PreservesColimitsOfSize.{0, 0} U := preservesColimitsOfSize_shrink U
  have : U.PreservesZeroMorphisms :=
    preservesZeroMorphisms_uliftForPresentationFunctor.{u, v, m, m, max u v m} (R := S)
  have : U.Full := full_uliftForPresentationFunctor S
  have : U.Faithful := faithful_uliftForPresentationFunctor S
  obtain ⟨hPd⟩ := nonempty_isColimit_map_freeCofan_of_equiv U (ULift.{m} (Fin n)) Equiv.ulift.symm
  obtain ⟨hQd⟩ := nonempty_isColimit_map_freeCofan_of_equiv U (ULift.{m} (Fin k)) Equiv.ulift.symm
  obtain ⟨eP⟩ : Nonempty (U.obj (free (ULift.{m} (Fin n))) ≅ P) :=
    ⟨hPd.coconePointUniqueUpToIso hP⟩
  obtain ⟨eQ⟩ : Nonempty (U.obj (free (ULift.{m} (Fin k))) ≅ Q) :=
    ⟨hQd.coconePointUniqueUpToIso hQ⟩
  obtain ⟨b₀, hb₀⟩ : ∃ b₀, U.map b₀ = eP.hom ≫ b := ⟨U.preimage _, U.map_preimage _⟩
  obtain ⟨a₀, ha₀⟩ : ∃ a₀, U.map a₀ = eQ.hom ≫ a ≫ eP.inv := ⟨U.preimage _, U.map_preimage _⟩
  have hab' : (eQ.hom ≫ a ≫ eP.inv) ≫ eP.hom ≫ b = 0 := by simp [hab]
  have hab₀ : a₀ ≫ b₀ = 0 := by
    refine U.map_injective ?_
    rw [Functor.map_zero, U.map_comp, ha₀, hb₀]
    exact hab'
  have key : ∀ {Z : SheafOfModules.{max u v m} S} (g : U.obj (free (ULift.{m} (Fin n))) ⟶ Z),
      (eQ.hom ≫ a ≫ eP.inv) ≫ g = 0 → a ≫ eP.inv ≫ g = 0 := by
    intro Z g hg
    refine (cancel_epi eQ.hom).mp ?_
    rw [comp_zero]
    simpa only [Category.assoc] using hg
  have H' : IsColimit (CokernelCofork.ofπ (eP.hom ≫ b) hab') := by
    refine CokernelCofork.IsColimit.ofπ _ _
      (fun {Z} g hg => (CokernelCofork.IsColimit.desc' hcok (eP.inv ≫ g) (key g hg)).1)
      (fun {Z} g hg => ?_) (fun {Z} g hg mm hm => ?_)
    · have hd := (CokernelCofork.IsColimit.desc' hcok (eP.inv ≫ g) (key g hg)).2
      simp only [CokernelCofork.π_ofπ] at hd ⊢
      rw [Category.assoc, hd, ← Category.assoc, eP.hom_inv_id, Category.id_comp]
    · have hd := (CokernelCofork.IsColimit.desc' hcok (eP.inv ≫ g) (key g hg)).2
      simp only [CokernelCofork.π_ofπ] at hd hm
      refine Cofork.IsColimit.hom_ext hcok ?_
      simp only [CokernelCofork.π_ofπ]
      rw [hd]
      refine (cancel_epi eP.hom).mp ?_
      have h2 : eP.hom ≫ eP.inv ≫ g = g := by simp
      rw [h2, ← Category.assoc]
      exact hm
  have key2 : ∀ {Z : SheafOfModules.{m} S} (g : free (ULift.{m} (Fin n)) ⟶ Z),
      a₀ ≫ g = 0 → (eQ.hom ≫ a ≫ eP.inv) ≫ U.map g = 0 := by
    intro Z g hg
    rw [← ha₀, ← U.map_comp, hg, Functor.map_zero]
  have hdesc : ∀ (Z : SheafOfModules.{m} S) (g : free (ULift.{m} (Fin n)) ⟶ Z),
      a₀ ≫ g = 0 → ∃ d : M ⟶ Z, b₀ ≫ d = g ∧ ∀ d' : M ⟶ Z, b₀ ≫ d' = g → d' = d := by
    intro Z g hg
    obtain ⟨e, he⟩ : ∃ e : U.obj M ⟶ U.obj Z, (eP.hom ≫ b) ≫ e = U.map g := by
      obtain ⟨e, he⟩ := CokernelCofork.IsColimit.desc' H' (U.map g) (key2 g hg)
      exact ⟨e, by simpa only [CokernelCofork.π_ofπ] using he⟩
    refine ⟨U.preimage e, ?_, ?_⟩
    · refine U.map_injective ?_
      rw [U.map_comp, U.map_preimage, hb₀]
      exact he
    · intro d' hd'
      have h5 : (eP.hom ≫ b) ≫ U.map d' = (eP.hom ≫ b) ≫ e := by
        refine Eq.trans ?_ he.symm
        calc (eP.hom ≫ b) ≫ U.map d' = U.map b₀ ≫ U.map d' :=
              congrArg (fun t => t ≫ U.map d') hb₀.symm
          _ = U.map (b₀ ≫ d') := (U.map_comp b₀ d').symm
          _ = U.map g := congrArg U.map hd'
      refine U.map_injective ?_
      rw [U.map_preimage]
      exact Cofork.IsColimit.hom_ext H' h5
  have Hdown : IsColimit (CokernelCofork.ofπ b₀ hab₀) :=
    CokernelCofork.IsColimit.ofπ _ _ (fun {Z} g hg => (hdesc Z g hg).choose)
      (fun {Z} g hg => (hdesc Z g hg).choose_spec.1)
      (fun {Z} g hg mm hm => (hdesc Z g hg).choose_spec.2 mm hm)
  exact ⟨presentationOfIsCokernelFree a₀ b₀ hab₀ Hdown,
    ⟨⟨Finite.of_equiv (Fin n) Equiv.ulift.symm⟩, ⟨Finite.of_equiv (Fin k) Equiv.ulift.symm⟩⟩⟩

omit [HasWeakSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}] in
/-- **Finite presentation on a site implies finite presentation in the sense of Mathlib**, in an
arbitrary module universe.

The covering family that Stacks 03DN asks for is the family of all objects on which the module
has a finite global presentation: by hypothesis every object of the site is covered by such
objects, so that family covers the final object, and on each of its members
`SheafOfModules.exists_isFinite_presentation_of_hasFiniteGlobalPresentation'` supplies a finite
presentation. -/
theorem isFinitePresentation_of_isFinitePresentationOnSite'
    [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{m}]
    [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{m}]
    (M : SheafOfModules.{m} S) (hM : M.IsFinitePresentationOnSite) :
    M.IsFinitePresentation := by
  rw [Stacks.SheafOfModules.isFinitePresentation_iff_exists_cover_finite_presentations]
  refine ⟨{V : C | (M.over V).HasFiniteGlobalPresentation}, fun i => i.1, ?_, fun i => ?_⟩
  · intro W
    obtain ⟨I, V, f, hV, hp⟩ := hM.locally_hasFiniteGlobalPresentation W
    have hRange : Set.range V ⊆
        Set.range (fun i : {V : C | (M.over V).HasFiniteGlobalPresentation} => i.1) := by
      rintro x ⟨i, rfl⟩
      exact ⟨⟨V i, hp i⟩, rfl⟩
    exact J.superset_covering
      ((Sieve.ofArrows_le_ofObjects V f).trans (Sieve.ofObjects_mono hRange)) hV
  · exact exists_isFinite_presentation_of_hasFiniteGlobalPresentation' (M := M.over i.1) i.2

end SheafOfModules

namespace Stacks.Sheaves.FinitePresentation

open AlgebraicGeometry Stacks.Sheaves.PresentationTransport
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback

universe v' u' w

/-- **Stacks 03DO for the clause 03DL(7), in the form stated with
`SheafOfModules.IsFinitePresentationOnSite`.**  The pullback
`f^*F = O_C ⊗_{f⁻¹O_D} f⁻¹F` of Stacks 03D6(2) of a sheaf of `O_D`-modules of finite
presentation on the site, along a morphism of ringed topoi, is again of finite presentation on
the site.

The two halves are the ones of
`Stacks.Sheaves.FinitePresentation.isFinitePresentation_pullbackModules`: the inverse image
produces a covering of each object of the source site on whose members `f⁻¹F` has a finite
presentation, and extension of scalars carries those presentations across `f⁻¹O_D ⟶ O_C`.  Only
the two ends differ, and they are the comparison of the two renderings of Stacks 03DL(7):
`SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite'` to enter and
`SheafOfModules.HasFiniteGlobalPresentation.of_presentation'` to leave. -/
theorem pullbackModules_isFinitePresentationOnSite
    {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w})]
    [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [HasWeakSheafify X.J AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ Z : X.C, HasWeakSheafify (X.J.over Z) AddCommGrpCat.{w}]
    [∀ Z : Y.C, HasWeakSheafify (Y.J.over Z) AddCommGrpCat.{w}]
    [∀ Z : X.C, (X.J.over Z).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ Z : Y.C, (Y.J.over Z).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (f : RingedToposHom X Y) (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hF : F.IsFinitePresentationOnSite) :
    ((f.pullbackModules).obj F).IsFinitePresentationOnSite := by
  have hFP : F.IsFinitePresentation :=
    SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite' F hF
  have := hFP
  refine ⟨fun V => ?_⟩
  obtain ⟨T, hT⟩ := exists_cover_isFinite_presentation_inverseImage f.toToposHom
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
    (pullbackModule X.J Y.J f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) F V
  refine ⟨Σ W : X.C, {g : W ⟶ V // T.1 g}, fun i => i.1, fun i => i.2.1, ?_, fun i => ?_⟩
  · refine X.J.superset_covering (fun Z g hg => ?_) T.2
    exact (Sieve.mem_ofArrows_iff _ _ _).2 ⟨⟨Z, g, hg⟩, 𝟙 Z, (Category.id_comp g).symm⟩
  · obtain ⟨P, hP⟩ := hT i.1 i.2.1 i.2.2
    exact SheafOfModules.HasFiniteGlobalPresentation.of_presentation'
      (presentationExtendScalarsOver (fSharpCommRing f)
        (ToposPushforward.inverseImageRingSheaf f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
        ((inverseImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F) i.1 P)
      (isFinite_presentationExtendScalarsOver (fSharpCommRing f) _ _ _ i.1 P hP)

end Stacks.Sheaves.FinitePresentation

end
