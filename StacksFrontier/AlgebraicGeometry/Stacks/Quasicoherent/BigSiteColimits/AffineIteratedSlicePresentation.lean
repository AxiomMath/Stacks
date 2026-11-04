module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence

/-!
# A global presentation on an iterated slice site is one on the slice at the underlying object

The slice of the slice site at `U` at an object `f : Over U` is equivalent, as a site, to the
slice site at the underlying object `f.left`, by `CategoryTheory.Over.iteratedSliceEquiv`.  The
coefficient sheaves of rings correspond under that equivalence by the identity, because the
sections of a restricted sheaf at an object of a slice are its sections at the underlying object,
so the equivalence of sites induces an equivalence of the categories of sheaves of modules.

`Stacks.SheafOfModules.hasGlobalPresentation_iteratedSlice` carries a global presentation across
that equivalence for a module of the form `M.over U`, obtained by restricting a module `M` on the
ambient site.  That is the shape it is needed in for Stacks 03DN, where the module is given on the
ambient site throughout.  It does not apply to an arbitrary sheaf of modules on the slice site at
`U`: the statement `(M.over f.left).HasGlobalPresentation` names a second restriction of the same
`M`, and a module given only on the slice has no such restriction.

That arbitrary case is what quasi-coherence on a slice site provides and what the essential
surjectivity of Stacks 03DX consumes: a quasi-coherent module on the slice site at an object has
global presentations on the *iterated* slices at the members of a covering family, while every
statement about affine objects of a slice of an fppf site is about a slice at an object of the
fibred category.  This file supplies it, by naming the transported module
`Stacks.SheafOfModules.iteratedSliceLeft` and carrying the presentation across with the same
argument.

## Main definitions

* `Stacks.SheafOfModules.iteratedSliceCompatibility`: the identity comparison exhibiting the
  coefficient sheaf of rings of the slice at `f.left` as the one of the iterated slice at `f`
  pushed forward along the equivalence of the two sites.
* `Stacks.SheafOfModules.iteratedSliceLeft`: **a sheaf of modules on the iterated slice site at
  `f : Over U`, read on the slice site at `f.left`.**

## Main results

* `Stacks.SheafOfModules.iteratedSliceLeft_val_obj`: the sections of the transported module are
  the sections of the original at the corresponding object, which is a definitional identity.
* `Stacks.SheafOfModules.hasGlobalPresentation_iteratedSliceLeft`: **a global presentation of a
  sheaf of modules on an iterated slice site is one of its reading on the slice site at the
  underlying object**, for an arbitrary module on the iterated slice.

## Implementation notes

The transport of a presentation along a functor preserving colimits and the structure sheaf is
carried out here rather than reused, because
`Stacks.SheafOfModules.hasGlobalPresentation_iteratedSlice` keeps that step private.  The two
auxiliary statements it needs — that a coproduct may be reindexed along an isomorphism of its
vertex, and that restriction commutes with the universe lift of the sections — are therefore
repeated as private declarations below; they are the same statements, and a public form of either
would make both copies unnecessary.

Mathlib's `SheafOfModules.Presentation` is not available here: it needs the universe of the
sections to contain those of the objects and of the morphisms of the site, while the sections of a
module on a slice of an fppf site live at the universe of the schemes and the fibred category is
at two independent universes.  That is the reason a presentation is transported through
`SheafOfModules.uliftForPresentation` rather than through `SheafOfModules.Presentation.map`.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SheafOfModules

universe u v w m

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})

/-- A coproduct remains one after composing every injection with an isomorphism of the common
source.  This is the reindexing needed to recognise the images of the tautological injections of a
coproduct of copies of the structure sheaf, after a functor has been applied, as injections out of
the structure sheaf itself. -/
private def isColimitCofanCompIso
    {D : Type*} [Category D] {I : Type*} {A A' Z : D} (e : A ≅ A') (f : I → (A' ⟶ Z))
    (h : IsColimit (Cofan.mk Z f)) : IsColimit (Cofan.mk Z fun i => e.hom ≫ f i) := by
  refine Cofan.IsColimit.mk _
    (fun s => Cofan.IsColimit.desc h fun i => e.inv ≫ s.inj i) ?_ ?_
  · intro s i
    simpa [Category.assoc] using
      congrArg (fun g => e.hom ≫ g) (Cofan.IsColimit.fac h (fun i => e.inv ≫ s.inj i) i)
  · intro s m hm
    apply Cofan.IsColimit.hom_ext h
    intro i
    have hi := hm i
    dsimp at hi
    rw [Cofan.IsColimit.fac h (fun i => e.inv ≫ s.inj i) i]
    simpa [Category.assoc] using congrArg (fun g => e.inv ≫ g) hi

/-- **A global presentation is carried by a functor preserving colimits and the structure
sheaf.**  The two coproducts of the presentation are carried to coproducts, the cokernel to a
cokernel, and the images of the copies of the structure sheaf are identified with copies of the
structure sheaf of the target by the given comparison.

The functor is given twice, at the universe of the sections and at the universe in which global
presentations are taken, together with the comparison `ηM` saying that the two agree on the
module: a presentation lives at the raised universe while its conclusion is about the module at
its own. -/
private theorem hasGlobalPresentation_mapOf {C' : Type u} [Category.{v} C']
    {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{w}}
    (M : _root_.SheafOfModules.{w} R)
    {F₀ : _root_.SheafOfModules.{w} R ⥤ _root_.SheafOfModules.{w} R'}
    {F : _root_.SheafOfModules.{max u v w} R ⥤ _root_.SheafOfModules.{max u v w} R'}
    [PreservesColimitsOfSize.{max u v w, max u v w} F] [Functor.PreservesZeroMorphisms F]
    (η₁ : F.obj (_root_.SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
        (_root_.SheafOfModules.unit R)) ≅
      _root_.SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
        (_root_.SheafOfModules.unit R'))
    (ηM : F.obj (_root_.SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} M) ≅
      _root_.SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} (F₀.obj M)) :
    M.HasGlobalPresentation → (F₀.obj M).HasGlobalPresentation := by
  classical
  let _ : PreservesColimitsOfSize.{0, 0} F := preservesColimitsOfSize_shrink F
  rintro ⟨I, K, P, Q, ι, κ, hP, hQ, a, b, hab, hc⟩
  have hcof : ∀ {I : Type (max u v w)} {P : _root_.SheafOfModules.{max u v w} R}
      (ι : ∀ _ : I, _root_.SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
        (_root_.SheafOfModules.unit R) ⟶ P), IsColimit (Cofan.mk P ι) →
      IsColimit (Cofan.mk (F.obj P) fun i => η₁.inv ≫ F.map (ι i)) := fun ι h =>
    isColimitCofanCompIso η₁.symm _
      ((Cofan.isColimitMapCoconeEquiv F _ (Cofan.mk _ ι)).toFun (isColimitOfPreserves F h))
  let b' : F.obj P ⟶ _root_.SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
      (F₀.obj M) := F.map b ≫ ηM.hom
  have hab' : F.map a ≫ b' = 0 := by simp [b', ← F.map_comp_assoc, hab]
  refine ⟨I, K, F.obj P, F.obj Q, _, _, ⟨hcof ι hP.some⟩, ⟨hcof κ hQ.some⟩, F.map a, b', hab',
    ⟨?_⟩⟩
  let d := parallelPair a 0 ⋙ F
  let i₁ : d ≅ parallelPair (F.map a) (F.map 0) := by
    refine NatIso.ofComponents (fun j => ?_) ?_
    · cases j <;> exact Iso.refl _
    rintro _ _ (_ | _ | _) <;> simp [d]
  let i₂ : parallelPair (F.map a) (F.map 0) ≅ parallelPair (F.map a) 0 :=
    parallelPairIsoMk (Iso.refl (F.obj Q)) (Iso.refl (F.obj P))
  let i := i₁ ≪≫ i₂
  exact (IsColimit.equivOfNatIsoOfIso i (F.mapCocone (CokernelCofork.ofπ b hab))
    (CokernelCofork.ofπ b' hab') (Cocone.ext ηM (by rintro (_ | _) <;>
      simp [b', d, i, i₁, i₂, parallelPairIsoMk, NatIso.ofComponents_inv_app]))).toFun
    (isColimitOfPreserves F hc.some)

/-- **Restriction along a continuous functor commutes with the universe lift of the sections**,
objectwise and by the identity.  A presentation is taken at a raised universe while the module it
presents lives at its own, so this comparison is what lets a transported presentation be read as
one of the transported module. -/
private noncomputable def pushforwardUliftComparison {C' : Type u} [Category.{v} C']
    {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{w}} {G : C' ⥤ C}
    [Functor.IsContinuous G J' J]
    (φ : R' ⟶ (G.sheafPushforwardContinuous RingCat.{w} J' J).obj R)
    (N : _root_.SheafOfModules.{w} R) :
    (_root_.SheafOfModules.pushforward.{max u v w} φ).obj
        (_root_.SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} N) ≅
      _root_.SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
        ((_root_.SheafOfModules.pushforward.{w} φ).obj N) :=
  (_root_.SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ => Iso.refl _) (by intro X Y f; ext x; rfl))

/-- The comparison exhibiting the coefficient sheaf of rings of the slice site at `f.left` as the
one of the iterated slice site at `f` pushed forward along
`CategoryTheory.Over.iteratedSliceEquiv`.  The sections of a restricted sheaf at an object of a
slice are its sections at the underlying object, so the two sheaves of rings are the same functor
and the comparison is the identity. -/
def iteratedSliceCompatibility (U : C) (f : Over U) :
    R.over f.left ⟶ ((Over.iteratedSliceEquiv f).inverse.sheafPushforwardContinuous
      RingCat.{w} (J.over f.left) ((J.over U).over f)).obj ((R.over U).over f) :=
  𝟙 _

/-- **A sheaf of modules on the iterated slice site at `f : Over U`, read on the slice site at
`f.left`.**  The two sites are equivalent by `CategoryTheory.Over.iteratedSliceEquiv` and their
coefficient sheaves of rings agree, so restriction along the inverse of that equivalence carries a
module on the one to a module on the other; its sections at an object are those of the original at
the corresponding object, by `Stacks.SheafOfModules.iteratedSliceLeft_val_obj`. -/
noncomputable abbrev iteratedSliceLeft (U : C) (f : Over U)
    (N : _root_.SheafOfModules.{m} ((R.over U).over f)) :
    _root_.SheafOfModules.{m} (R.over f.left) :=
  (_root_.SheafOfModules.pushforward.{m} (iteratedSliceCompatibility R U f)).obj N

/-- The sections of a module read on the slice site at the underlying object are its sections at
the corresponding object of the iterated slice site, and the two are the same module: restriction
along the inverse of the equivalence of the two sites changes neither the object it is evaluated
at nor the ring acting on the result.

The equation is definitional and is stated so that a consumer may rewrite with it rather than
unfold the restriction. -/
lemma iteratedSliceLeft_val_obj (U : C) (f : Over U)
    (N : _root_.SheafOfModules.{m} ((R.over U).over f)) (Z : Over f.left) :
    (iteratedSliceLeft R U f N).val.obj (op Z) =
      N.val.obj (op ((Over.iteratedSliceEquiv f).inverse.obj Z)) :=
  rfl

/-- **A global presentation of a sheaf of modules on an iterated slice site is one of its reading
on the slice site at the underlying object.**

The two sites are equivalent by `CategoryTheory.Over.iteratedSliceEquiv`, the two coefficient
sheaves of rings are the same functor, and restriction along the inverse of the equivalence is
therefore one half of an equivalence of the two categories of sheaves of modules; an equivalence
preserves colimits and zero morphisms and carries the structure sheaf to the structure sheaf, so
it carries the two coproducts and the cokernel of a presentation.

Unlike `Stacks.SheafOfModules.hasGlobalPresentation_iteratedSlice` the module is arbitrary on the
iterated slice rather than a second restriction of a module on the ambient site, which is the form
quasi-coherence of a module given only on a slice site supplies. -/
theorem hasGlobalPresentation_iteratedSliceLeft (U : C) (f : Over U)
    (N : _root_.SheafOfModules.{w} ((R.over U).over f)) (h : N.HasGlobalPresentation) :
    (iteratedSliceLeft R U f N).HasGlobalPresentation := by
  let ψ := iteratedSliceCompatibility R U f
  let F := _root_.SheafOfModules.pushforward.{max u v w} ψ
  let _ : F.IsLeftAdjoint :=
    (_root_.SheafOfModules.pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv f) (𝟙 _) ψ
      (by ext : 2; exact R.1.map_id _)
      (by ext : 2; exact R.1.map_id _)).symm.isLeftAdjoint_functor
  let _ : F.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  exact hasGlobalPresentation_mapOf ((R.over U).over f) N
    (pushforwardUliftComparison ((R.over U).over f) ψ
      (_root_.SheafOfModules.unit ((R.over U).over f)))
    (pushforwardUliftComparison ((R.over U).over f) ψ N) h

end Stacks.SheafOfModules

end
