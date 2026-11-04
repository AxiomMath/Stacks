module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackQuasicoherence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Global presentations, restriction to a slice site, and pullback along a morphism of ringed topoi

A sheaf of modules on a ringed site *has a global presentation* when it is the cokernel of a
morphism between two coproducts of copies of the structure sheaf; Stacks 03DL (6) calls it
*quasi-coherent* when it has a global presentation on the members of a covering of each object of
the site.  Mathlib spells one such cokernel diagram as a `SheafOfModules.Presentation` — a family
of global sections generating the module together with a family generating the kernel of the
resulting morphism out of the free module — while `SheafOfModules.HasGlobalPresentation` spells it
by universal properties, after a universe lift which bounds the two index types.

This file proves that a global presentation passes to a slice site, and draws from that the
quasi-coherent clause of Stacks 03DO for a module that has a global presentation outright.  The
one step of that clause which does **not** follow is isolated as a hypothesis:
`Stacks.Sheaves.Quasicoherence.isQuasicoherentOnSite_pullbackModules_of_mapData` says that
supplying the localization of the morphism of ringed topoi finishes it.

## Main definitions

* `Stacks.SheafOfModules.presentationOver`: on a site whose slices are essentially small in the
  universe of the module sections, a `SheafOfModules.Presentation` of `M` gives one of `M`
  restricted to a slice site.

## Main results

* `Stacks.SheafOfModules.hasGlobalPresentation_over`: **a global presentation passes to a slice
  site**, with no hypothesis on the site and with the universes of the site independent of the
  universe of the module sections.
* `Stacks.SheafOfModules.hasFiniteGlobalPresentation_over` and
  `Stacks.SheafOfModules.hasFiniteGlobalGenerators_over`: the same for finite global
  presentations and finite families of global generators, whence
  `Stacks.SheafOfModules.isFinitePresentationOnSite_of_hasFiniteGlobalPresentation` and
  `Stacks.SheafOfModules.isFiniteTypeOnSite_of_hasFiniteGlobalGenerators`.
* `Stacks.SheafOfModules.isQuasicoherentOnSite_of_hasGlobalPresentation` and
  `Stacks.SheafOfModules.isQuasicoherentOnSite_of_presentation`: a sheaf of modules with a global
  presentation is quasi-coherent on the site.
* `Stacks.SheafOfModules.isQuasicoherentOnSite_of_quasicoherentData` and
  `Stacks.SheafOfModules.nonempty_quasicoherentData_of_isQuasicoherentOnSite`: Mathlib's
  `SheafOfModules.QuasicoherentData` and `SheafOfModules.IsQuasicoherentOnSite` agree, the second
  implication on a site whose slices are essentially small in the universe of the sections.
* `Stacks.SheafOfModules.isQuasicoherentOnSite_of_mapData` and
  `Stacks.SheafOfModules.isQuasicoherentOnSite_of_forall_mapData`: a functor admitting a
  `Stacks.SheafOfModules.QuasicoherentData.MapData` carries quasi-coherence on the site to
  quasi-coherence on the site.
* `Stacks.Sheaves.Quasicoherence.presentationInverseImageModules`: a global presentation of `F`
  transported along the inverse image of Stacks 03D2.
* `Stacks.Sheaves.Quasicoherence.isQuasicoherentOnSite_pullbackModules_of_presentation`:
  **the quasi-coherent clause of Stacks 03DO for a module with a global presentation.** The
  pullback `f^*F = O_C ⊗_{f⁻¹O_D} f⁻¹F` of Stacks 03D6 (2) of a sheaf of `O_D`-modules admitting
  a `SheafOfModules.Presentation` is quasi-coherent.
* `Stacks.Sheaves.Quasicoherence.inverseImageLocallyPresented_of_presentation`: the
  inverse-image factor of that clause, discharged on the trivial covering for a module with a
  global presentation.
* `Stacks.Sheaves.Quasicoherence.isQuasicoherentOnSite_pullbackModules_of_mapData` and
  `Stacks.Sheaves.Quasicoherence.isQuasicoherentOnSite_pullbackModules_of_forall_mapData`: **the
  quasi-coherent clause of Stacks 03DO, reduced to the localization of `f`.** The second takes
  its hypothesis in the form the clause states it — `F` quasi-coherent — and is the clause itself
  granted the localization of a morphism of ringed topoi.

## Implementation notes

**Why the slice statement is made for `HasGlobalPresentation` and not for `Presentation`.**
Transporting a `SheafOfModules.Presentation` along a functor asks that functor to preserve
colimits, and restriction to a slice site is `SheafOfModules.pushforward` along
`CategoryTheory.Over.forget`, which Mathlib makes a left adjoint only when the underlying functor
of sites is one — for `Over.forget` that needs binary products in the site.  The route that needs
no hypothesis on the site passes instead through the pushforward of *abelian* sheaves along
`Over.forget`, a left adjoint because `Over.forget` is cocontinuous; but its right adjoint is a
Kan extension, so that adjunction exists only at a universe of sections containing the universes
of the site.  `SheafOfModules.HasGlobalPresentation` is stated after exactly such a universe
lift, which is why `Stacks.SheafOfModules.hasGlobalPresentation_over` holds with the universes of
the site and of the module sections independent, while
`Stacks.SheafOfModules.presentationOver` — which has to come back down — needs the slice to be
essentially small in the universe of the sections, through
`Stacks.SheafOfModules.nonempty_presentation_of_hasGlobalPresentation`.

**What the quasi-coherent clause of Stacks 03DO needs, and where it is supplied.** The
statements below transport one
global presentation along one functor, and that is all pullback can do unaided: the presentations
of a quasi-coherent `F` live on a covering of the *target* site, while quasi-coherence of `f^*F`
asks for presentations on a covering of the *source* site, and a morphism of topoi carries no
objects of one site to objects of the other.  Carrying a presentation across requires, for a
member `V` of a covering of an object of the source site, a colimit-preserving functor from
modules on the slice at some member `W` of the given covering of the target site to modules on
the slice at `V`, agreeing with `f^*` at `F`; that is the content of
`Stacks.SheafOfModules.QuasicoherentData.MapData`, and the functor it asks for is the pullback
along the localized morphism of ringed topoi, i.e. the content of Section 03DG of the source.
Nothing here constructs it, and `isQuasicoherentOnSite_pullbackModules_of_mapData` is the precise
statement that it is the only thing the clause is missing.  That datum is now built, for the
case Section 03DG reduces to — a morphism of ringed *sites* presented by a left exact continuous
functor — as `Stacks.Sheaves.LocalizedPullback.localizedPullbackMapData` in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LocalizedPullbackQuasicoherent.lean`, out of the
pullback along the localized morphism of ringed topoi of Stacks 04J0; the reduction of an
arbitrary morphism of ringed topoi to that case is the square of Stacks 03CR, carried out in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LocalTypesToposPullback.lean`.  So the clause is
proved, and the hypothesis of the statements below is no longer open — it is simply not
discharged *here*.  Section 03DG is in addition carried out for the
special case of a comparison presented by a special cocontinuous functor of sites, in
`StacksFrontier.CategoryTheory.Sites.Topos.LocalizedSpecialCocontinuous`, whose
`Stacks.LocalizedDenseSubsite.sliceEquivalence` is the localized functor for that case.  The
sibling clause 03DL (7) escapes
this because a *finite* presentation is recorded by the sections of a sheaf of sets indexed by
`ℕ × ℕ`, which does transport along `f⁻¹`; see the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposPullbackQuasicoherence.lean`.

**No tag attribute is carried here.** Every statement below about pullback either assumes a
global presentation of `F` or assumes the localization data, so none of them states a clause of
Stacks 03DO.  The clause 03DO (6) itself is
`AlgebraicGeometry.RingedToposHom.isQuasicoherentOnSite_pullbackModules`, which carries its
attribute alongside the clauses (1), (2) and (3) in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LocalTypesToposPullback.lean`; the remaining three
clauses carry theirs at
`Stacks.Sheaves.LocalGeneration.pullbackModules_isLocallyGeneratedByOnSite` (4),
`Stacks.Sheaves.FiniteType.pullbackModules_isFiniteType` (5) and
`Stacks.Sheaves.FinitePresentation.isFinitePresentation_pullbackModules` (7).

## References

* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DF](https://stacks.math.columbia.edu/tag/03DF)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModules

/-! ### A global presentation passes to a slice site -/

section Over

universe u v w s t

/-- Restriction to a slice site commutes with the universe lift of the module sections: both are
the identity on sections. -/
private noncomputable def overUliftIso {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}} (U : C)
    (N : _root_.SheafOfModules.{s} R) :
    (_root_.SheafOfModules.overFunctor.{max t s} R U).obj
        (_root_.SheafOfModules.uliftForPresentation.{u, v, w, s, t} N) ≅
      _root_.SheafOfModules.uliftForPresentation.{max u v, v, w, s, t}
        ((_root_.SheafOfModules.overFunctor.{s} R U).obj N) :=
  (_root_.SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ => Iso.refl _) (by
      intro X Y f
      ext x
      rfl))

/-- Precomposing the inclusions of a coproduct with an isomorphism of the summand leaves a
coproduct. -/
private noncomputable def isColimitCofanPrecomposeIso {D : Type*} [Category D] {I : Type*}
    {A B Z : D} (e : A ≅ B) (g : I → (B ⟶ Z)) (h : IsColimit (Cofan.mk Z g)) :
    IsColimit (Cofan.mk Z (fun i => e.hom ≫ g i)) := by
  refine Cofan.IsColimit.mk _ (fun s =>
    Cofan.IsColimit.desc h (fun i => e.inv ≫ s.inj i)) ?_ ?_
  · intro s i
    simpa [Category.assoc] using
      congrArg (fun k => e.hom ≫ k)
        (Cofan.IsColimit.fac h (fun i => e.inv ≫ s.inj i) i)
  · intro s m hm
    apply Cofan.IsColimit.hom_ext h
    intro i
    have hi := hm i
    dsimp at hi
    rw [Cofan.IsColimit.fac h (fun i => e.inv ≫ s.inj i) i]
    simpa [Category.assoc] using congrArg (fun k => e.inv ≫ k) hi

/-- A colimit-preserving functor carries a coproduct cofan to a coproduct cofan, after precomposing
the inclusions with an isomorphism onto the image of the summand. -/
private noncomputable def isColimitCofanMapPrecompose {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {I : Type*} [PreservesColimitsOfShape (Discrete I) F] {A P : C} {B : D}
    (e : B ≅ F.obj A) (ι : I → (A ⟶ P)) (h : IsColimit (Cofan.mk P ι)) :
    IsColimit (Cofan.mk (F.obj P) (fun i => e.hom ≫ F.map (ι i))) :=
  isColimitCofanPrecomposeIso e _
    ((Cofan.isColimitMapCoconeEquiv F _ (Cofan.mk P ι)).toFun (isColimitOfPreserves F h))

/-- The covering of an object by itself, indexed by a single member, is covering. -/
private theorem ofArrows_id_mem {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (U : C) :
    Sieve.ofArrows (fun _ : ULift.{max u v} PUnit => U) (fun _ => 𝟙 U) ∈ J U :=
  J.superset_covering (fun _ g _ => (Sieve.mem_ofArrows_iff ..).mpr
    ⟨ULift.up PUnit.unit, g, by simp⟩) (J.top_mem U)

/-- **A global presentation passes to a slice site.** If a sheaf of modules is the cokernel of a
morphism between coproducts of copies of the structure sheaf, then so is its restriction to the
site over any object.  This is the global half of Stacks 03DF for the quasi-coherent clause of
Stacks 03DL (6).

Nothing is assumed of the site, and the universes of the site are independent of the universe of
the module sections: the restriction functor is applied at the lifted universe at which
`SheafOfModules.HasGlobalPresentation` takes its coproducts, and there restriction does preserve
colimits by `Stacks.SheafOfModules.overFunctor_preservesColimits`.  Restriction also preserves
the zero morphism and commutes with the universe lift, so the whole cokernel diagram travels. -/
theorem hasGlobalPresentation_over {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} (M : _root_.SheafOfModules.{t} R) (U : C)
    (h : M.HasGlobalPresentation) : (M.over U).HasGlobalPresentation := by
  classical
  let F := _root_.SheafOfModules.overFunctor.{max u v w t} R U
  let _ : PreservesColimitsOfSize.{max u v w t, max u v w t} F :=
    overFunctor_preservesColimits.{u, v, w, t} R U
  let _ : F.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  let _ : PreservesColimitsOfSize.{0, 0} F := preservesColimitsOfSize_shrink F
  let η₁ : F.obj (_root_.SheafOfModules.uliftForPresentation.{u, v, w, w, max u v t}
      (_root_.SheafOfModules.unit R)) ≅
      _root_.SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v t}
        (_root_.SheafOfModules.unit (R.over U)) :=
    overUliftIso.{u, v, w, w, max u v t} U (_root_.SheafOfModules.unit R)
  let ηM : F.obj (_root_.SheafOfModules.uliftForPresentation.{u, v, w, t, max u v w} M) ≅
      _root_.SheafOfModules.uliftForPresentation.{max u v, v, w, t, max u v w} (M.over U) :=
    overUliftIso.{u, v, w, t, max u v w} U M
  obtain ⟨I, K, P, Q, ι, κ, hP, hQ, a, b, hab, hc⟩ := h
  let ι' : ∀ _ : I, _root_.SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v t}
      (_root_.SheafOfModules.unit (R.over U)) ⟶ F.obj P := fun i => η₁.inv ≫ F.map (ι i)
  let κ' : ∀ _ : K, _root_.SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v t}
      (_root_.SheafOfModules.unit (R.over U)) ⟶ F.obj Q := fun i => η₁.inv ≫ F.map (κ i)
  have hP' : Nonempty (IsColimit (Cofan.mk (F.obj P) ι')) :=
    ⟨isColimitCofanMapPrecompose F η₁.symm ι hP.some⟩
  have hQ' : Nonempty (IsColimit (Cofan.mk (F.obj Q) κ')) :=
    ⟨isColimitCofanMapPrecompose F η₁.symm κ hQ.some⟩
  let b' : F.obj P ⟶ _root_.SheafOfModules.uliftForPresentation.{max u v, v, w, t, max u v w}
      (M.over U) := F.map b ≫ ηM.hom
  have hab' : F.map a ≫ b' = 0 := by
    simp only [b', ← Category.assoc, ← F.map_comp, hab, F.map_zero, zero_comp]
  exact ⟨I, K, F.obj P, F.obj Q, ι', κ', hP', hQ', F.map a, b', hab',
    ⟨(isColimitCoforkMapOfIsColimit' F hab hc.some).ofIsoColimit (Cofork.ext ηM (by simp [b']))⟩⟩

section Finite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{w}} (M : _root_.SheafOfModules.{t} R)

/-- **A finite global presentation passes to a slice site.** If a sheaf of modules is the
cokernel of a morphism between finite coproducts of copies of the structure sheaf, then so is its
restriction to the site over any object, with the same numbers of generators and relations.

The proof is that of `Stacks.SheafOfModules.hasGlobalPresentation_over`: restriction preserves
colimits at the lifted universe of the coproducts
(`Stacks.SheafOfModules.overFunctor_preservesColimits`), preserves zero morphisms and commutes
with the universe lift, so the whole cokernel diagram travels. -/
theorem hasFiniteGlobalPresentation_over (U : C) (h : M.HasFiniteGlobalPresentation) :
    (M.over U).HasFiniteGlobalPresentation := by
  classical
  let F := _root_.SheafOfModules.overFunctor.{max u v w t} R U
  let _ : PreservesColimitsOfSize.{max u v w t, max u v w t} F :=
    overFunctor_preservesColimits.{u, v, w, t} R U
  let _ : F.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  let _ : PreservesColimitsOfSize.{0, 0} F := preservesColimitsOfSize_shrink F
  let η₁ : F.obj (_root_.SheafOfModules.uliftForPresentation.{u, v, w, w, max u v t}
      (_root_.SheafOfModules.unit R)) ≅
      _root_.SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v t}
        (_root_.SheafOfModules.unit (R.over U)) :=
    overUliftIso.{u, v, w, w, max u v t} U (_root_.SheafOfModules.unit R)
  let ηM : F.obj (_root_.SheafOfModules.uliftForPresentation.{u, v, w, t, max u v w} M) ≅
      _root_.SheafOfModules.uliftForPresentation.{max u v, v, w, t, max u v w} (M.over U) :=
    overUliftIso.{u, v, w, t, max u v w} U M
  obtain ⟨n, k, P, Q, ι, κ, hP, hQ, a, b, hab, hc⟩ := h
  let ι' : ∀ _ : Fin n, _root_.SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v t}
      (_root_.SheafOfModules.unit (R.over U)) ⟶ F.obj P := fun i => η₁.inv ≫ F.map (ι i)
  let κ' : ∀ _ : Fin k, _root_.SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v t}
      (_root_.SheafOfModules.unit (R.over U)) ⟶ F.obj Q := fun i => η₁.inv ≫ F.map (κ i)
  have hP' : Nonempty (IsColimit (Cofan.mk (F.obj P) ι')) :=
    ⟨isColimitCofanMapPrecompose F η₁.symm ι hP.some⟩
  have hQ' : Nonempty (IsColimit (Cofan.mk (F.obj Q) κ')) :=
    ⟨isColimitCofanMapPrecompose F η₁.symm κ hQ.some⟩
  let b' : F.obj P ⟶ _root_.SheafOfModules.uliftForPresentation.{max u v, v, w, t, max u v w}
      (M.over U) := F.map b ≫ ηM.hom
  have hab' : F.map a ≫ b' = 0 := by
    simp only [b', ← Category.assoc, ← F.map_comp, hab, F.map_zero, zero_comp]
  exact ⟨n, k, F.obj P, F.obj Q, ι', κ', hP', hQ', F.map a, b', hab',
    ⟨(isColimitCoforkMapOfIsColimit' F hab hc.some).ofIsoColimit (Cofork.ext ηM (by simp [b']))⟩⟩

/-- **Finite global generators pass to a slice site.** If a finite coproduct of copies of the
structure sheaf maps epimorphically onto a sheaf of modules, then the same holds for its
restriction to the site over any object, with the same number of generators.

Restriction preserves colimits at the lifted universe of the coproduct
(`Stacks.SheafOfModules.overFunctor_preservesColimits`), hence the finite coproduct and, being
colimit-preserving, epimorphisms; it commutes with the universe lift of the module sections. -/
theorem hasFiniteGlobalGenerators_over (U : C) (h : M.HasFiniteGlobalGenerators) :
    (M.over U).HasFiniteGlobalGenerators := by
  classical
  let F := _root_.SheafOfModules.overFunctor.{max u v w t} R U
  let _ : PreservesColimitsOfSize.{max u v w t, max u v w t} F :=
    overFunctor_preservesColimits.{u, v, w, t} R U
  let _ : PreservesColimitsOfSize.{0, 0} F := preservesColimitsOfSize_shrink F
  let _ : F.PreservesEpimorphisms := preservesEpimorphisms_of_preservesColimitsOfShape F
  let η₁ : F.obj (_root_.SheafOfModules.uliftForPresentation.{u, v, w, w, max u v t}
      (_root_.SheafOfModules.unit R)) ≅
      _root_.SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v t}
        (_root_.SheafOfModules.unit (R.over U)) :=
    overUliftIso.{u, v, w, w, max u v t} U (_root_.SheafOfModules.unit R)
  let ηM : F.obj (_root_.SheafOfModules.uliftForPresentation.{u, v, w, t, max u v w} M) ≅
      _root_.SheafOfModules.uliftForPresentation.{max u v, v, w, t, max u v w} (M.over U) :=
    overUliftIso.{u, v, w, t, max u v w} U M
  obtain ⟨n, P, ι, hP, π, hπ⟩ := h
  exact ⟨n, F.obj P, fun i => η₁.inv ≫ F.map (ι i),
    ⟨isColimitCofanMapPrecompose F η₁.symm ι hP.some⟩,
    F.map π ≫ ηM.hom, inferInstance⟩

/-- **A sheaf of modules with a finite global presentation is of finite presentation on the
site.** The covering of an object witnessing finite presentation may be taken to be the
identity, and the finite global presentation passes to the slice site by
`Stacks.SheafOfModules.hasFiniteGlobalPresentation_over`. -/
theorem isFinitePresentationOnSite_of_hasFiniteGlobalPresentation
    (h : M.HasFiniteGlobalPresentation) : M.IsFinitePresentationOnSite where
  locally_hasFiniteGlobalPresentation U :=
    ⟨ULift.{max u v} PUnit, fun _ => U, fun _ => 𝟙 U,
      ofArrows_id_mem J U,
      fun _ => hasFiniteGlobalPresentation_over M U h⟩

/-- **A sheaf of modules with finite global generators is of finite type on the site.** The
covering of an object witnessing finite type may be taken to be the identity, and the finite
global generators pass to the slice site by
`Stacks.SheafOfModules.hasFiniteGlobalGenerators_over`. -/
theorem isFiniteTypeOnSite_of_hasFiniteGlobalGenerators
    (h : M.HasFiniteGlobalGenerators) : M.IsFiniteTypeOnSite where
  locally_finitelyGenerated U :=
    ⟨ULift.{max u v} PUnit, fun _ => U, fun _ => 𝟙 U,
      ofArrows_id_mem J U,
      fun _ => hasFiniteGlobalGenerators_over M U h⟩

end Finite

end Over

/-! ### Quasi-coherence on the site from a global presentation -/

section Quasicoherent

universe u v r m ww

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- **A sheaf of modules with a global presentation is quasi-coherent on the site.** The covering
of an object witnessing quasi-coherence may be taken to be the identity, and the global
presentation passes to the slice site by
`Stacks.SheafOfModules.hasGlobalPresentation_over`. -/
theorem isQuasicoherentOnSite_of_hasGlobalPresentation (M : _root_.SheafOfModules.{m} R)
    (h : M.HasGlobalPresentation.{u, v, r, m}) : M.IsQuasicoherentOnSite where
  locally_hasGlobalPresentation U :=
    ⟨ULift.{max u v} PUnit, fun _ => U, fun _ => 𝟙 U,
      ofArrows_id_mem J U,
      fun _ => hasGlobalPresentation_over M U h⟩

variable [HasWeakSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]

/-- **A sheaf of modules with a `SheafOfModules.Presentation` is quasi-coherent on the site.**
Mathlib's encoding of a global presentation is converted to the universal-property one by
`Stacks.SheafOfModules.hasGlobalPresentation_of_presentation`. -/
theorem isQuasicoherentOnSite_of_presentation {M : _root_.SheafOfModules.{r} R}
    (P : M.Presentation) : M.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_hasGlobalPresentation M
    (hasGlobalPresentation_of_presentation P)

/-- **A global presentation restricted to a slice site.** On a site whose slice over `V` is
essentially small in the universe of the module sections, a `SheafOfModules.Presentation` of `M`
gives one of `M` restricted to the slice over `V`.

The essential smallness is what
`Stacks.SheafOfModules.nonempty_presentation_of_hasGlobalPresentation` needs in order to produce
index types in the universe of the sections, and it is the only hypothesis beyond the ones
`SheafOfModules.Presentation` itself carries; the underlying transport of the cokernel diagram,
`Stacks.SheafOfModules.hasGlobalPresentation_over`, needs none. -/
theorem presentationOver {M : _root_.SheafOfModules.{r} R} (P : M.Presentation) (V : C)
    [∀ W : C, HasWeakSheafify (J.over W) AddCommGrpCat.{r}]
    [∀ W : C, (J.over W).WEqualsLocallyBijective AddCommGrpCat.{r}]
    [EssentiallySmall.{r} (Over V)] : Nonempty ((M.over V).Presentation) :=
  nonempty_presentation_of_hasGlobalPresentation
    (hasGlobalPresentation_over M V (hasGlobalPresentation_of_presentation P))

omit [HasWeakSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
/-- **Mathlib's quasi-coherent data gives quasi-coherence on the site.** A
`SheafOfModules.QuasicoherentData` is a family of objects covering the terminal object together
with a `SheafOfModules.Presentation` of the module restricted to each of them, and
`Stacks.SheafOfModules.hasGlobalPresentation_of_presentation` turns each of those into a
`SheafOfModules.HasGlobalPresentation`.  The index type is moved into the universe of the objects
of the site by `SheafOfModules.QuasicoherentData.shrink`. -/
theorem isQuasicoherentOnSite_of_quasicoherentData {M : _root_.SheafOfModules.{r} R}
    [∀ W : C, HasWeakSheafify (J.over W) AddCommGrpCat.{r}]
    [∀ W : C, (J.over W).WEqualsLocallyBijective AddCommGrpCat.{r}]
    (q : M.QuasicoherentData.{ww}) : M.IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation M).2
    ⟨q.shrink.I, q.shrink.X, q.shrink.coversTop,
      fun i => hasGlobalPresentation_of_presentation (q.shrink.presentation i)⟩

omit [HasWeakSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
/-- **Quasi-coherence on the site gives Mathlib's quasi-coherent data**, on a site whose slices
are essentially small in the universe of the module sections.  This is the converse of
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_quasicoherentData`, and the essential smallness
is used only to turn each `SheafOfModules.HasGlobalPresentation` back into a
`SheafOfModules.Presentation`, whose index types must live in the universe of the sections. -/
theorem nonempty_quasicoherentData_of_isQuasicoherentOnSite (M : _root_.SheafOfModules.{r} R)
    [∀ W : C, HasWeakSheafify (J.over W) AddCommGrpCat.{r}]
    [∀ W : C, (J.over W).WEqualsLocallyBijective AddCommGrpCat.{r}]
    [∀ W : C, EssentiallySmall.{r} (Over W)]
    (hM : M.IsQuasicoherentOnSite) : Nonempty (M.QuasicoherentData.{u}) := by
  obtain ⟨I, U, hU, hP⟩ := (isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation M).1 hM
  exact ⟨{ I := I, X := U, coversTop := hU
           presentation := fun i => (nonempty_presentation_of_hasGlobalPresentation (hP i)).some }⟩

end Quasicoherent

/-! ### Quasi-coherence on the site transported along a functor -/

section Map

universe u v u₁ v' u' ww

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C} {S : Sheaf J RingCat.{u}}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D} {R : Sheaf K RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{u}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : D, HasWeakSheafify (K.over W) AddCommGrpCat.{u}]
  [∀ W : D, (K.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {F : _root_.SheafOfModules.{u} R ⥤ _root_.SheafOfModules.{u} S}
  {M : _root_.SheafOfModules.{u} R}

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Quasi-coherence on the site is preserved by a functor admitting a `MapData`.** This is the
quasi-coherent counterpart of `Stacks.SheafOfModules.isFinitePresentation_of_mapData`: the
transported quasi-coherent data of `Stacks.SheafOfModules.QuasicoherentData.map` is turned into
quasi-coherence on the site by
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_quasicoherentData`. -/
theorem isQuasicoherentOnSite_of_mapData {q : M.QuasicoherentData.{ww}}
    (L : QuasicoherentData.MapData F q) : (F.obj M).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_quasicoherentData (QuasicoherentData.map q L)

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Quasi-coherence on the site is preserved by a functor admitting a `MapData` for every
quasi-coherent datum.** The quasi-coherent counterpart of
`Stacks.SheafOfModules.isFinitePresentation_of_forall_mapData`: the hypothesis is quasi-coherence
on the site, with no datum supplied by the caller, and the slices of the source site are asked to
be essentially small in the universe of the module sections so that
`Stacks.SheafOfModules.nonempty_quasicoherentData_of_isQuasicoherentOnSite` can produce one. -/
theorem isQuasicoherentOnSite_of_forall_mapData [∀ W : D, EssentiallySmall.{u} (Over W)]
    (hM : M.IsQuasicoherentOnSite)
    (L : ∀ q : M.QuasicoherentData.{u'}, QuasicoherentData.MapData F q) :
    (F.obj M).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_mapData
    (L (nonempty_quasicoherentData_of_isQuasicoherentOnSite M hM).some)

end Map

end Stacks.SheafOfModules

namespace Stacks.Sheaves.Quasicoherence

/-! ### Pullback along a morphism of ringed topoi: the globally presented case -/

section Global

open AlgebraicGeometry Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.FinitePresentation

universe v u v' u' w

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y)

/-- The inverse image of sheaves of modules along a morphism of topoi preserves colimits, being
a left adjoint (Stacks 03D3). -/
@[sga "4 IV 13.6" "special case"]
instance preservesColimitsOfSize_inverseImageModules :
    PreservesColimitsOfSize.{w, w}
      (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  (inverseImageAdjDirectImageModules f.toToposHom
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).leftAdjoint_preservesColimits

/-- **A global presentation transported along the inverse image of Stacks 03D2.** A
`SheafOfModules.Presentation` of a sheaf of `O_D`-modules `F` gives one of the inverse image
`f⁻¹F`, as a sheaf of `f⁻¹O_D`-modules, with the *same* index types for the generators and the
relations: the inverse image is a left adjoint, hence preserves the cokernel diagram, and it
carries `O_D` to `f⁻¹O_D` on the nose
(`Stacks.Sheaves.FinitePresentation.inverseImageModulesUnitIso`). -/
noncomputable def presentationInverseImageModules
    {F : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (P : F.Presentation) :
    ((inverseImageModules f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F).Presentation :=
  let _ : HasSheafify X.J AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let _ : HasSheafify Y.J AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  P.map (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (inverseImageModulesUnitIso f)

/-- **The quasi-coherent clause of Stacks 03DO for a module with a global presentation.** The
pullback `f^*F = O_C ⊗_{f⁻¹O_D} f⁻¹F` of Stacks 03D6 (2) of a sheaf of `O_D`-modules admitting a
`SheafOfModules.Presentation` is quasi-coherent.

The presentation is carried along the pullback by
`Stacks.Sheaves.FinitePresentation.presentationPullbackModules`, which is available because
pullback is a left adjoint and carries `O_D` to `O_C`, and the resulting global presentation
makes `f^*F` quasi-coherent by
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_presentation`.

Quasi-coherence of `F` alone does not suffice for this argument, and supplying it is the whole
of what Stacks 03DO (6) adds; see the implementation notes of this file. -/
theorem isQuasicoherentOnSite_pullbackModules_of_presentation
    {F : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (P : F.Presentation) :
    ((f.pullbackModules).obj F).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_presentation
    (presentationPullbackModules f P)

/-- **The inverse-image factor of the quasi-coherent clause of Stacks 03DO, for a module with a
global presentation.** If `F` admits a `SheafOfModules.Presentation` then the inverse image
`f⁻¹F` of Stacks 03D2 admits one over *every* object of the source site, so the covering asked
for by
`Stacks.Sheaves.Quasicoherence.isQuasicoherentOnSite_pullbackModules_of_inverseImage_local` may
be taken to be the trivial one.

This is the form in which a consumer carrying that factor as a hypothesis — such as
`AlgebraicGeometry.Space.InverseImageLocallyPresented` — can discharge it.  The slices of the
source site are asked to be essentially small in the universe of the module sections, which is
what `Stacks.SheafOfModules.presentationOver` needs to produce a `SheafOfModules.Presentation`
rather than a `SheafOfModules.HasGlobalPresentation` on the slice. -/
theorem inverseImageLocallyPresented_of_presentation
    [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
    [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ U : X.C, EssentiallySmall.{w} (Over U)]
    (F : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (P : F.Presentation) (U : X.C) :
    ∃ T : X.J.Cover U, ∀ (V : X.C) (g : V ⟶ U), T g →
      Nonempty ((((inverseImageModules f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F).over V).Presentation) :=
  ⟨⟨⊤, X.J.top_mem U⟩, fun V _ _ =>
    Stacks.SheafOfModules.presentationOver (presentationInverseImageModules f P) V⟩

end Global

/-! ### Pullback along a morphism of ringed topoi: the clause, reduced to the localization -/

section Reduction

open AlgebraicGeometry Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe v u v' u' w ww

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ W : Y.C, HasWeakSheafify (Y.J.over W) AddCommGrpCat.{w}]
  [∀ W : Y.C, (Y.J.over W).WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- **The quasi-coherent clause of Stacks 03DO, reduced to the localization of `f`.** Let `F` be
a sheaf of `O_D`-modules with quasi-coherent data `q` — a covering family of the target site
together with a global presentation of `F` on each member.  Suppose given a covering family of
the source site and, for each of its members `V`, a member `W` of `q`'s family together with a
colimit-preserving functor `Mod(O_D|_W) ⥤ Mod(O_C|_V)` carrying `O_D|_W` to `O_C|_V` and `F|_W`
to `(f^*F)|_V`.  Then `f^*F` is quasi-coherent.

That functor is the pullback along the morphism of ringed topoi
`(Sh(C/V), O_C|_V) ⟶ (Sh(D/W), O_D|_W)` obtained by localizing `f`, which is the content of
Section 03DG of the source; nothing in this development constructs it, and this statement is
exactly the assertion that it is the only thing the clause still needs. -/
theorem isQuasicoherentOnSite_pullbackModules_of_mapData
    {F : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    {q : F.QuasicoherentData.{ww}}
    (L : Stacks.SheafOfModules.QuasicoherentData.MapData (f.pullbackModules) q) :
    ((f.pullbackModules).obj F).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_mapData L

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- **The quasi-coherent clause of Stacks 03DO, reduced to the localization of `f`, for a
quasi-coherent module.** This is
`Stacks.Sheaves.Quasicoherence.isQuasicoherentOnSite_pullbackModules_of_mapData` with the
hypothesis in the form the clause states it: `F` is quasi-coherent, and the localization data is
supplied for every quasi-coherent datum of `F` rather than for one chosen in advance.

Granted the localization of a morphism of ringed topoi — Section 03DG of the source — this *is*
the quasi-coherent clause of Stacks 03DO. The slices of the target site are asked to be
essentially small in the universe of the module sections, which is what recovers a
`SheafOfModules.Presentation` from the `SheafOfModules.HasGlobalPresentation` that
`SheafOfModules.IsQuasicoherentOnSite` records. -/
theorem isQuasicoherentOnSite_pullbackModules_of_forall_mapData
    [∀ W : Y.C, EssentiallySmall.{w} (Over W)]
    (F : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hF : F.IsQuasicoherentOnSite)
    (L : ∀ q : F.QuasicoherentData.{u'},
      Stacks.SheafOfModules.QuasicoherentData.MapData (f.pullbackModules) q) :
    ((f.pullbackModules).obj F).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_forall_mapData hF L

end Reduction

end Stacks.Sheaves.Quasicoherence

end
