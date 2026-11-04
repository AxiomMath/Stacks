module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ModulePullback
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlas
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite

/-!
# Coherent modules on a locally Noetherian algebraic stack (Stacks 0GR7, 0GR8)

Let `𝒳` be a locally Noetherian algebraic stack.  Stacks 0GR6 calls an `𝒪_𝒳`-module *coherent*
when it satisfies the equivalent conditions of Stacks 0GR5; the condition used here is
Stacks 0GR5(2), that the module be an `𝒪_𝒳`-module **of finite presentation** in the sense of
Stacks 03DL(7), namely `SheafOfModules.IsFinitePresentationOnSite` for the structure sheaf of the
big fppf site of `𝒳`.  It is the condition through which the source itself proves both results
below: 0GR7 by exhibiting a finite presentation locally and 0GR8 because pullback along a
morphism of ringed topoi preserves finitely presented modules.

Of Stacks 0GR7 the clauses proved here are that `𝒪_𝒳` is coherent and that every finite locally
free `𝒪_𝒳`-module is coherent.  The remaining clause, that every *invertible* `𝒪_𝒳`-module is
coherent, is proved in
`StacksFrontier/AlgebraicGeometry/Stacks/InvertibleCoherent.lean`, by a different route: on a
general site an invertible module need not be finite locally free (Stacks 0B8M).

## Main definitions

* `AlgebraicGeometry.Stack.IsCoherentModule`: coherence of a module on an algebraic stack, read
  as the finite-presentation condition Stacks 0GR5(2).

## Main results

* `SheafOfModules.isFiniteLocallyFreeOnSite_unit` and
  `SheafOfModules.isFinitePresentationOnSite_unit`: the structure sheaf of any ringed site, as a
  module over itself, is finite locally free of rank one and hence of finite presentation.
* `SheafOfModules.HasFiniteGlobalPresentation.of_iso` and
  `SheafOfModules.IsFinitePresentationOnSite.of_iso`: both conditions are invariant under
  isomorphism of modules.
* `SheafOfModules.hasFiniteGlobalPresentation_restrictAlongContinuous` and
  `SheafOfModules.isFinitePresentationOnSite_restrictAlongContinuous`: restriction of modules
  along a continuous functor with a left adjoint preserves finite global presentations, and
  preserves finite presentation on the site when the slices of the functor are equivalences.
* `SheafOfModules.isFinitePresentationOnSite_of_restrictionIso`: a module isomorphic, after the
  change of scalars identifying the two structure presheaves, to such a restriction is of finite
  presentation.
* `AlgebraicGeometry.Stack.isFinitePresentationOnSite_modulePullback`: the inverse image of
  modules along a 1-morphism of categories fibred in groupoids preserves finite presentation.
* `AlgebraicGeometry.Stack.isCoherentModule_unit` and
  `AlgebraicGeometry.Stack.isCoherentModule_of_isFiniteLocallyFreeOnSite`: **Stacks 0GR7**, the
  structure-sheaf clause and the finite locally free clause.  The invertible-module clause is
  `AlgebraicGeometry.Stack.isCoherentModule_of_isInvertible`.
* `AlgebraicGeometry.Stack.isCoherentModule_modulePullback`: **Stacks 0GR8**.

## Implementation notes

`IsCoherentModule` carries no `@[stacks]` attribute.  Stacks 0GR6 defines coherence by reference
to the equivalence of the four conditions of Stacks 0GR5, and that equivalence is not proved
here; what is recorded is one of the four conditions, so the definition is not the source's
definition and does not realize its tag.  Both results below therefore read coherence as
Stacks 0GR5(2), and each is in fact a statement about finite presentation on the fppf site of
the stack.

Local Noetherianity of the stack is an explicit hypothesis of both statements, as in the source,
and is unused: on a general ringed site the structure sheaf is of finite presentation, finite
local freeness implies finite presentation, and finite presentation is preserved by the inverse
image.  In the source it is needed only to know that the four conditions of Stacks 0GR5 agree,
which is what makes "coherent" well defined.

The generic results on restriction are the finite refinements of
`SheafOfModules.hasGlobalPresentation_restrictAlongContinuous` and
`SheafOfModules.isQuasicoherentOnSite_restrictAlongContinuous`, and the 1-morphism statement is
the finite refinement of Stacks 06WH at
`AlgebraicGeometry.Stack.isQuasicoherentOnSite_modulePullback`.  The index types of the
generators and of the relations are `Fin n` and `Fin k` on the nose, so a left adjoint carries a
finite presentation to a finite presentation with the same two numbers and no reindexing is
needed; everything else is as in the quasi-coherent case, the covering of an object of the source
site coming from cocontinuity and the slice equivalences of Stacks 06W0.

As in the quasi-coherent case, the inverse-image statements hold for modules whose sections lie
in the universe `max u v w m` of the objects and the morphisms of the two sites, their
coefficient rings and the sections: a finite global presentation is a diagram in that universe,
so the restriction functor has to be read there.  For an algebraic stack the objects of the fppf
site are one universe above the schemes, which is why Stacks 0GR8 is stated for modules with
sections in `max (u + 1) m`.  The two clauses of Stacks 0GR7 carry no such restriction, the
finite locally free clause holding at an arbitrary module universe and the structure-sheaf clause
at the universe of the coefficient rings.

## References

* [Stacks Project, Tag 0GR5](https://stacks.math.columbia.edu/tag/0GR5)
* [Stacks Project, Tag 0GR6](https://stacks.math.columbia.edu/tag/0GR6)
* [Stacks Project, Tag 0GR7](https://stacks.math.columbia.edu/tag/0GR7)
* [Stacks Project, Tag 0GR8](https://stacks.math.columbia.edu/tag/0GR8)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 06WH](https://stacks.math.columbia.edu/tag/06WH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w m t

namespace SheafOfModules

section SingleSite

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- Having a finite global presentation is invariant under isomorphism: compose the presenting
cokernel map with the universe lift of the isomorphism, which changes neither the number of
generators nor the number of relations. -/
theorem HasFiniteGlobalPresentation.of_iso {M N : SheafOfModules.{m} R} (e : M ≅ N)
    (h : HasFiniteGlobalPresentation M) : HasFiniteGlobalPresentation N := by
  obtain ⟨n, k, P, Q, ι, κ, hP, hQ, a, b, hab, ⟨hb⟩⟩ := h
  refine ⟨n, k, P, Q, ι, κ, hP, hQ, a, b ≫ (uliftForPresentationMapIso e).hom, ?_, ⟨?_⟩⟩
  · rw [← Category.assoc, hab, zero_comp]
  · exact hb.ofIsoColimit (Cofork.ext (uliftForPresentationMapIso e) rfl)

/-- Finite presentation of a module on a site is invariant under isomorphism: restriction to a
slice site is a functor, so an isomorphism restricts to one on every member of a covering. -/
theorem IsFinitePresentationOnSite.of_iso {M N : SheafOfModules.{m} R} (e : M ≅ N)
    (h : M.IsFinitePresentationOnSite) : N.IsFinitePresentationOnSite where
  locally_hasFiniteGlobalPresentation U := by
    obtain ⟨I, V, f, hcover, hpres⟩ := h.locally_hasFiniteGlobalPresentation U
    exact ⟨I, V, f, hcover,
      fun i ↦ .of_iso ((SheafOfModules.overFunctor R (V i)).mapIso e) (hpres i)⟩

/-- The structure sheaf of a site, viewed as a module over itself, is finite locally free: over
the covering family generated by the identity of an object it is the coproduct of a single copy
of itself. -/
theorem isFiniteLocallyFreeOnSite_unit :
    (SheafOfModules.unit R).IsFiniteLocallyFreeOnSite := by
  refine (isFiniteLocallyFreeOnSite_iff_exists_cover_isColimit (SheafOfModules.unit R)).mpr
    fun U ↦ ?_
  refine ⟨PUnit.{max v w + 1}, fun _ ↦ U, fun _ ↦ 𝟙 U, ?_, fun _ ↦ ⟨1, fun _ ↦ 𝟙 _, ?_⟩⟩
  · have htop : Sieve.ofArrows (fun _ : PUnit.{max v w + 1} ↦ U) (fun _ ↦ 𝟙 U) = ⊤ := by
      refine eq_top_iff.mpr fun Z g _ ↦ ?_
      have h := Sieve.ofArrows_mk (fun _ : PUnit.{max v w + 1} ↦ U) (fun _ ↦ 𝟙 U) PUnit.unit
      simpa using
        (Sieve.ofArrows (fun _ : PUnit.{max v w + 1} ↦ U) (fun _ ↦ 𝟙 U)).downward_closed h g
    rw [htop]
    exact J.top_mem U
  · refine ⟨{ desc := fun s ↦ s.ι.app ⟨0⟩, fac := ?_, uniq := ?_ }⟩
    · rintro s ⟨j⟩
      obtain rfl : j = 0 := Subsingleton.elim _ _
      exact Category.id_comp _
    · exact fun s g h ↦ (Category.id_comp g).symm.trans (h ⟨0⟩)

/-- The structure sheaf of a site, viewed as a module over itself, is of finite presentation: it
is finite locally free. -/
theorem isFinitePresentationOnSite_unit :
    (SheafOfModules.unit R).IsFinitePresentationOnSite :=
  isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite isFiniteLocallyFreeOnSite_unit

end SingleSite

section Restrict

variable {C D : Type v} [Category.{w} C] [Category.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (G : C ⥤ D) [G.IsContinuous J K] (R : Sheaf K RingCat.{u})

/-- Restriction along a continuous functor with a left adjoint preserves finite global
presentations: being a left adjoint it preserves the two finite coproducts and the cokernel that
make up the presentation, and the index types `Fin n` and `Fin k` are unchanged. -/
theorem hasFiniteGlobalPresentation_restrictAlongContinuous [G.IsCocontinuous J K]
    [G.IsLeftAdjoint] (M : SheafOfModules.{max u v w m} R)
    (hM : M.HasFiniteGlobalPresentation) :
    ((restrictAlongContinuous (J := J) G R).obj M).HasFiniteGlobalPresentation := by
  let L : SheafOfModules.{max u v w m} R ⥤ _ := restrictAlongContinuous (J := J) G R
  have : L.IsLeftAdjoint := isLeftAdjoint_restrictAlongContinuous G R
  obtain ⟨n, k, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hb⟩⟩ := hM
  refine ⟨n, k, L.obj P, L.obj Q, (fun i ↦ L.map (ι i)),
    (fun i ↦ L.map (κ i)), ⟨isColimitCofanMkObjOfIsColimit L _ _ hP⟩,
    ⟨isColimitCofanMkObjOfIsColimit L _ _ hQ⟩,
    L.map a, L.map b, (L.map_comp a b).symm.trans (congrArg L.map hab), ?_⟩
  exact ⟨isColimitCoforkMapOfIsColimit' L hab hb⟩

/-- Restriction along a continuous and cocontinuous functor whose slice functors are equivalences
preserves finite presentation on the site.

A covering of `G.obj U` on whose members `M` has a finite global presentation is lifted by
cocontinuity to a covering of `U`; the slice equivalence turns each of its members into an object
`A i` of `C` over `U` whose image is the member, and restriction along the slice functor at
`A i` is again a restriction along a continuous functor with a left adjoint, so it preserves the
presentation. -/
theorem isFinitePresentationOnSite_restrictAlongContinuous [G.IsCocontinuous J K]
    (hG : ∀ U : C, (Over.post (X := U) G).IsEquivalence)
    (M : SheafOfModules.{max u v w m} R) [M.IsFinitePresentationOnSite] :
    ((restrictAlongContinuous (J := J) G R).obj M).IsFinitePresentationOnSite := by
  constructor
  intro U
  obtain ⟨I, V, f, hf, hV⟩ :=
    IsFinitePresentationOnSite.locally_hasFiniteGlobalPresentation (F := M) (G.obj U)
  have := hG U
  let E := (Over.post (X := U) G).asEquivalence
  let A (i : I) : Over U := E.inverse.obj (Over.mk (f i))
  let e (i : I) : (Over.post G).obj (A i) ≅ Over.mk (f i) := E.counitIso.app _
  refine ⟨I, (fun i ↦ (A i).left), (fun i ↦ (A i).hom), ?_, ?_⟩
  · apply J.superset_covering _ (G.cover_lift J K hf)
    intro W a ha
    obtain ⟨i, b, he⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp ha
    let k : (Over.post G).obj (Over.mk a) ⟶ (Over.post G).obj (A i) :=
      Over.homMk (V := Over.mk (f i)) b he.symm ≫ (e i).inv
    let l : Over.mk a ⟶ A i := (Over.post G).preimage k
    exact (Sieve.mem_ofArrows_iff _ _ _).mpr ⟨i, l.left, (Over.w l).symm⟩
  · intro i
    let ei : G.obj (A i).left ⟶ V i := (e i).hom.left
    let H : Over (A i).left ⥤ Over (V i) := Over.post G ⋙ Over.map ei
    have := hG (A i).left
    have : (Over.post (X := (A i).left) G).IsContinuous
        (J.over (A i).left) (K.over (G.obj (A i).left)) :=
      Functor.isContinuous_iff_coverPreserving.mpr
        ((CoverPreserving.of_isContinuous G J K).overPost _)
    have : H.IsContinuous (J.over (A i).left) (K.over (V i)) := by
      dsimp only [H]
      infer_instance
    have : H.IsCocontinuous (J.over (A i).left) (K.over (V i)) :=
      isCocontinuous_comp (Over.post G) (Over.map ei)
        (J.over (A i).left) (K.over (G.obj (A i).left))
    have : IsIso ei :=
      inferInstanceAs (IsIso ((Over.forget (G.obj U)).map (e i).hom))
    have : H.IsEquivalence := inferInstance
    exact hasFiniteGlobalPresentation_restrictAlongContinuous.{u, max v w, w, m}
      H (R.over (V i)) (M.over (V i)) (hV i)

/-- A module whose underlying presheaf of modules is isomorphic to the restriction along `G` of a
module of finite presentation, with scalars transported along the equality of the two structure
presheaves, is itself of finite presentation. -/
theorem isFinitePresentationOnSite_of_restrictionIso
    (T : Sheaf J RingCat.{u}) (hT : T.obj = G.op ⋙ R.obj)
    (M : SheafOfModules.{m} R) (N : SheafOfModules.{m} T)
    (e : N.val ≅ (PresheafOfModules.pushforward₀ G R.obj ⋙
      PresheafOfModules.restrictScalars (eqToHom hT)).obj M.val)
    [((restrictAlongContinuous (J := J) G R).obj M).IsFinitePresentationOnSite] :
    N.IsFinitePresentationOnSite := by
  have hs : T = (G.sheafPushforwardContinuous RingCat.{u} J K).obj R :=
    ObjectProperty.FullSubcategory.ext hT
  subst T
  let e' : N ≅ (restrictAlongContinuous (J := J) G R).obj M :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso e
  exact IsFinitePresentationOnSite.of_iso e'.symm ‹_›

end Restrict

end SheafOfModules

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inverse image of modules along a 1-morphism of categories fibred in groupoids over the
big fppf category of `S` preserves finite presentation on the site.

This is the finite refinement of Stacks 06WH: the inverse image is
`AlgebraicGeometry.Stack.modulePullback`, which on underlying presheaves of modules is
restriction along the 1-morphism followed by the change of scalars identifying the two structure
presheaves, and the slices of a 1-morphism of categories fibred in groupoids are equivalences by
Stacks 06W0. -/
theorem isFinitePresentationOnSite_modulePullback
    {𝒳 𝒴 : Type v} [Category.{w} 𝒳] [Category.{w} 𝒴]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p)
    (M : SheafOfModules.{max u v w m}
      (ringStructureSheafCore B S hS q hq B.topology le_rfl))
    [M.IsFinitePresentationOnSite] :
    ((modulePullback.{u, v, w, max u v w m} B S hS p q hp hq f hf
      B.topology le_rfl).obj M).IsFinitePresentationOnSite := by
  have hF : p.IsFibredOneMorphism q f := hq.isFibredOneMorphism hf
  have : p.IsFibered := hp.isFibered
  have : q.IsFibered := hq.isFibered
  let J := associatedTopology B S hS p B.topology
  let K := associatedTopology B S hS q B.topology
  have : f.IsContinuous J K :=
    (hF.isContinuous_and_isCocontinuous_inheritedTopology (B.topology.over (B.obj hS))).1
  have : f.IsCocontinuous J K :=
    (hF.isContinuous_and_isCocontinuous_inheritedTopology (B.topology.over (B.obj hS))).2
  have hslice : ∀ U : 𝒳, (Over.post (X := U) f).IsEquivalence := by
    intro U
    subst p
    let r := q ⋙ Over.forget (B.obj hS)
    have : (Over.post (X := f.obj U) r).IsEquivalence :=
      isEquivalence_overPost B S hS q hq (f.obj U)
    have : (Over.post (X := U) (f ⋙ r)).IsEquivalence :=
      isEquivalence_overPost B S hS (f ⋙ q) hp U
    have : (Over.post (X := U) f ⋙ Over.post r).IsEquivalence := by
      rw [← Over.post_comp]
      infer_instance
    exact Functor.isEquivalence_of_comp_right (Over.post f) (Over.post r)
  let R := ringStructureSheafCore B S hS q hq B.topology le_rfl
  have : ((SheafOfModules.restrictAlongContinuous (J := J) f R).obj M).IsFinitePresentationOnSite :=
    SheafOfModules.isFinitePresentationOnSite_restrictAlongContinuous.{u, v, w, m} f R hslice M
  let W := moduleSheafFunctoriality.{u, v, w, m, v, w} B S hS p q hp hq f hf
    B.topology le_rfl
  exact SheafOfModules.isFinitePresentationOnSite_of_restrictionIso f R _
    (ringStructureSheafCore_obj_eq B S hS p q hp hq f hf B.topology le_rfl) M
    (W.pullback.obj M) (W.pullback_iso.app M)

/-- **Stacks 0GR6 read as Stacks 0GR5(2).**  A module on the big fppf site of an algebraic stack
`𝒳` is *coherent* when it is of finite presentation as a module on that ringed site, which is
condition (2) of Stacks 0GR5.

This carries no tag: Stacks 0GR6 defines coherence by the equivalence of the four conditions of
Stacks 0GR5, and that equivalence is not proved here. -/
abbrev IsCoherentModule (𝒳 : AlgebraicStacks.{u, t} B S hS)
    (M : SheafOfModules.{m} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)) : Prop :=
  M.IsFinitePresentationOnSite

/-- **Stacks 0GR7, the structure-sheaf clause.**  On a locally Noetherian algebraic stack the
module `𝒪_𝒳` is coherent: on any site the structure sheaf viewed as a module over itself is the
coproduct of one copy of itself, hence of finite presentation.

Local Noetherianity is the hypothesis of the source and is not used; see the module
documentation. -/
@[stacks 0GR7 "the structure sheaf of the stack is coherent"]
theorem isCoherentModule_unit (𝒳 : AlgebraicStacks.{u, t} B S hS)
    (_h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳) :
    IsCoherentModule B S hS 𝒳 (SheafOfModules.unit _) :=
  SheafOfModules.isFinitePresentationOnSite_unit

/-- **Stacks 0GR7, the finite locally free clause.**  On a locally Noetherian algebraic stack
every finite locally free `𝒪_𝒳`-module is coherent: the covering witnessing finite local freeness
already carries a finite global presentation on each of its members.

Local Noetherianity is the hypothesis of the source and is not used. -/
@[stacks 0GR7 "finite locally free modules on the stack are coherent"]
theorem isCoherentModule_of_isFiniteLocallyFreeOnSite (𝒳 : AlgebraicStacks.{u, t} B S hS)
    (_h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    (M : SheafOfModules.{m} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl))
    (hM : M.IsFiniteLocallyFreeOnSite) :
    IsCoherentModule B S hS 𝒳 M :=
  SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite hM

/-- **Stacks 0GR8.**  For a 1-morphism `f : 𝒳 ⟶ 𝒴` of locally Noetherian algebraic stacks, the
inverse image `f^*` sends coherent modules on `𝒴` to coherent modules on `𝒳`.

Coherence is Stacks 0GR5(2), finite presentation on the fppf site, and the inverse image of
modules along a 1-morphism preserves it.  Local Noetherianity of the two stacks is the hypothesis
of the source and is not used. -/
@[stacks 0GR8]
theorem isCoherentModule_modulePullback (𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS) (f : 𝒳 ⟶ 𝒴)
    (_h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    (_h𝒴 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒴)
    (M : SheafOfModules.{max (u + 1) m} (ringStructureSheafCore B S hS 𝒴.val.val.p
      𝒴.val.isFiberedInGroupoids B.topology le_rfl))
    (hM : IsCoherentModule B S hS 𝒴 M) :
    IsCoherentModule B S hS 𝒳
      ((modulePullback B S hS 𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids
        𝒴.val.isFiberedInGroupoids f.hom.hom.toFunctor f.hom.hom.w
        B.topology le_rfl).obj M) := by
  have := hM
  exact isFinitePresentationOnSite_modulePullback B S hS 𝒳.val.val.p 𝒴.val.val.p
    𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids f.hom.hom.toFunctor
    f.hom.hom.w M

end AlgebraicGeometry.Stack

end
