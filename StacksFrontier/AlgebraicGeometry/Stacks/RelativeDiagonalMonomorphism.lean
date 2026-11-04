module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.MorphismRepresentableBySpaces.Criterion
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeProperty

/-!
# The relative diagonal of a representable morphism of stacks is a monomorphism (Stacks 04YQ)

Let `S` be a scheme contained in a big fppf site `B` and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks over the big fppf site of `S` which is representable by algebraic spaces. Its
relative diagonal

`Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳`

is representable by algebraic spaces (Stacks 04XS, part (1)), so the relative properties of
Stacks 03YK make sense for it. This file proves two of the five parts of **Stacks 04YQ** for it:
part (3), that `Δ_f` is a monomorphism, and part (4), that `Δ_f` is separated.

The source's proof of part (3) is read off the cartesian square labelled 04XT: for a
scheme-valued point `a = (x, x', α)` of `𝒳 ×_𝒴 𝒳` over `T`, the fibre
`𝒳 ×_{𝒳 ×_𝒴 𝒳, a} T` is `Isom_𝒳(x, x') ×_{Isom_𝒴(f x, f x'), α} T`, and the right vertical
arrow `Isom_𝒳(x, x') ⟶ Isom_𝒴(f x, f x')` is injective as a map of sheaves because `f` is
representable by algebraic spaces — this is the faithfulness clause of **Stacks 02ZY**. So the
left vertical arrow, a base change of it, is a monomorphism. Part (4) is then Stacks 042N: the
diagonal of a monomorphism is an isomorphism, hence a closed immersion.

## Main results

* `AlgebraicGeometry.Stack.mono_relativeDiagonal_of_isRepresentableByAlgebraicSpaces`:
  **Stacks 04YQ, part (3)**.
* `AlgebraicGeometry.Stack.isSeparated_relativeDiagonal_of_isRepresentableByAlgebraicSpaces`:
  **Stacks 04YQ, part (4)**.
* `AlgebraicGeometry.Stack.subsingleton_representing_of_relativeDiagonal`: the step with the
  mathematical content — every algebraic space representing the base change of `Δ_f` along a
  scheme-valued point of `𝒳 ×_𝒴 𝒳` takes subsingleton values.
* `AlgebraicGeometry.Space.isSeparated_of_mono`: **Stacks 042N**, a monomorphism of algebraic
  spaces is separated.

## Implementation notes

The §04XB quantifier is written out longhand rather than through
`AlgebraicGeometry.Stack.HasRelativeProperty`, because that abbreviation carries two instance
arguments on the property — stability under base change and locality at the target for the fppf
precoverage — which it does not use, so the longhand form is the same `Prop` with no hypothesis
on the property at all. For a monomorphism the locality instance is not available, and
hypothesising it would weaken the statements for nothing.

The passage from a representing presheaf over `U` to an algebraic space over `S` with a morphism
to the representable space of `U` is `AlgebraicGeometry.spacesOverSmallerBaseFunctor`, the
forward functor of Stacks 04SG, exactly as `AlgebraicGeometry.Stack.HasRelativeProperty` uses it.

The chain from the square 04XT to the conclusion is three steps. The fibre of `Δ_f` over a point
`Y` of `𝒳 ×_𝒴 𝒳` is the category of elements of the presheaf of vertical morphisms over the
comparison isomorphism of `Y` — `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre`, the
criterion recorded as
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_iff`.
That presheaf has at most one section over each object, because two sections have the same image
under `f`. Transporting along the universe-lifted comparison isomorphism makes the representing
presheaf subsingleton-valued, and then the structural morphism of its lower-shriek extension is
injective section by section: a section of the extension over `W` is a factorization
`ψ : W ⟶ U` together with a section of the representing presheaf over `ψ`, and the structural
morphism returns `ψ`.

`CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.subsingleton_relVertHom_of_faithful`
and `AlgebraicGeometry.presheaf_of_isIso` are general statements whose natural homes are
`StacksFrontier/CategoryTheory/FiberedInGroupoids/Representability/RelativeDiagonalFibre.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/Category.lean` (beside `presheaf_id_of_iso`, of which the
second is the generalisation from the identity of a representable presheaf to an arbitrary
isomorphism of presheaves); they are stated here, where they are used.

`AlgebraicGeometry.Space.isSeparated_of_mono` is Stacks 042N, Chapter 67. It is proved here
because Stacks 04YQ part (4) consumes it, and it carries the tag: the statement — a
monomorphism of algebraic spaces is separated — is the whole of 042N, in the generality of an
arbitrary morphism of presheaves on the big fppf site of `S`. The remaining Chapter 67 results
about monomorphisms are in
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/Monomorphisms.lean`, which does not restate it.

## References

* [Stacks Project, Tag 04YQ](https://stacks.math.columbia.edu/tag/04YQ)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04XT](https://stacks.math.columbia.edu/tag/04XT)
* [Stacks Project, Tag 02ZY](https://stacks.math.columbia.edu/tag/02ZY)
* [Stacks Project, Tag 042N](https://stacks.math.columbia.edu/tag/042N)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {X : Type u₃} [Category.{v₃} X]
  {𝒯 : Type u₂} [Category.{v₂} 𝒯] {𝒴 : Type u₄} [Category.{v₄} 𝒴]
variable {p : X ⥤ 𝒞} {p𝒯 : 𝒯 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {F : X ⥤ 𝒴}
variable {Y : 𝒯 ⥤ RelProd p q F}

/-- **The left vertical arrow of the square 04XT is injective on sections.** If the functor
induced by `F` on the fibre over `p𝒯 a` is faithful, the presheaf of vertical morphisms
`Y₁ a ⟶ Y₂ a` lying over the comparison isomorphism of `Y` has at most one section over `a`:
two such sections have the same image under `F`, namely that comparison isomorphism. -/
lemma subsingleton_relVertHom_of_faithful (hF : F ⋙ q = p) (a : 𝒯)
    (hfaith : (Stacks.RepresentableMorphism.inducedFiberFunctor p q F hF (p𝒯.obj a)).Faithful) :
    Subsingleton (RelVertHom p𝒯 Y a) :=
  ⟨fun m n => RelVertHom.ext
    (Stacks.RepresentableMorphism.fiberHom_injective_of_inducedFiberFunctor_faithful p q F hF
      (p𝒯.obj a) hfaith
      m.1.1 n.1.1 m.1.2 n.1.2 (m.2.trans n.2.symm))⟩

end CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A property of morphisms of the big fppf site of `S` which holds for all isomorphisms is
inherited, in the sense of `CategoryTheory.MorphismProperty.presheaf`, by any isomorphism of
presheaves. This generalises `AlgebraicGeometry.presheaf_id_of_iso` from the identity of a
representable presheaf to an arbitrary isomorphism. -/
theorem presheaf_of_isIso (P : MorphismProperty (BigFppfOver B S hS))
    (hP : ∀ ⦃X Y⦄ (f : X ⟶ Y), IsIso f → P f)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : F ⟶ G) (hg : IsIso g) :
    P.presheaf g := by
  have := hg
  refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, ?_⟩
  intro A C h fst snd hpb
  have : IsIso (yoneda.map snd) := hpb.isIso_snd_of_isIso
  have : IsIso snd := Functor.FullyFaithful.isIso_of_isIso_map Yoneda.fullyFaithful snd
  exact hP snd ‹IsIso snd›

namespace Space

/-- **Stacks 042N.** A monomorphism of algebraic spaces over `S` is separated: its relative
diagonal is an isomorphism, and an isomorphism is a closed immersion.

The statement is made for an arbitrary morphism of presheaves on the big fppf site of `S`; no
algebraic-space hypothesis is used. -/
@[stacks 042N, stacks 0463 "separatedness"]
theorem isSeparated_of_mono {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : F ⟶ G) (hg : Mono g) :
    IsSeparated B S hS g := by
  have := hg
  refine presheaf_of_isIso B S hS _ ?_ (pullback.diagonal g) inferInstance
  intro X Y a ha
  have := ha
  show AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map a)
  infer_instance

end Space

/-- The structural morphism of the lower-shriek extension of a subsingleton-valued algebraic
space over `U` is injective on sections: a section of the extension over `W` is a factorization
`ψ : W ⟶ U` of the structural morphism of `W` together with a section over `ψ`, and the
structural morphism returns `ψ`. -/
theorem mono_hom_algebraicSpaceMap_of_subsingleton (U : BigFppfOver B S hS)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (hsub : ∀ V, Subsingleton (F.obj V)) :
    Mono (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom := by
  rw [NatTrans.mono_iff_mono_app]
  intro W
  rw [mono_iff_injective]
  set e := (spacesOverSmallerBaseFunctorForgetIso B U.left.1 S U.left.2 hS U.hom).inv.app
    (⟨F, hF⟩ : AlgebraicSpaces B U.left.1 U.left.2) with he
  have hiso : IsIso e := by rw [he]; infer_instance
  have hsurj : Function.Surjective (ConcreteCategory.hom (e.app W)) :=
    (ConcreteCategory.bijective_of_isIso (e.app W)).2
  refine Function.Injective.of_comp_right ?_ hsurj
  intro s s' hss
  have key : ∀ t, (ConcreteCategory.hom
      ((algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom.app W))
      ((ConcreteCategory.hom (e.app W)) t) = Over.homMk t.1.1 t.2 := fun t =>
    spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app B U.left.1 S U.left.2 hS U.hom
      ⟨F, hF⟩ W t
  simp only [Function.comp_apply, key] at hss
  apply Subtype.ext
  obtain ⟨⟨ψ, t⟩, hψ⟩ := s
  obtain ⟨⟨ψ', t'⟩, hψ'⟩ := s'
  have hfst : ψ = ψ' := congrArg (fun m => m.left) hss
  subst hfst
  have hs2 : Subsingleton (F.obj (op (Over.mk ψ))) := hsub _
  exact congrArg (Sigma.mk ψ) (Subsingleton.elim (α := F.obj (op (Over.mk ψ))) t t')

/-- A subsingleton-valued algebraic space over `U`, read as an algebraic space over `S` with a
morphism to the representable algebraic space of `U`, has monomorphic structural morphism.
This is `AlgebraicGeometry.mono_hom_algebraicSpaceMap_of_subsingleton` read in the category of
algebraic spaces over `S`, where it is the form the relative properties of Stacks 03YK are
stated in. -/
theorem mono_algebraicSpaceMap_of_subsingleton (U : BigFppfOver B S hS)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (hsub : ∀ V, Subsingleton (F.obj V)) :
    Mono (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)) :=
  (ObjectProperty.ι _).mono_of_mono_map
    (mono_hom_algebraicSpaceMap_of_subsingleton B S hS U F hF hsub)

namespace Stack

universe v w t

open CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

/-- **The content of Stacks 04YQ parts (3)–(5): the fibres of the relative diagonal are
subobjects of their bases.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids
over the big fppf site of `S` which is representable by algebraic spaces, let `U` be a scheme
over `S` and let `y` be a scheme-valued point of `𝒳 ×_{f, 𝒴, f} 𝒳` over the big fppf site of
`U`. Then every algebraic space `F` over `U` representing the base change of the relative
diagonal of `f` along `y` takes subsingleton values.

The square 04XT identifies `F` with the presheaf of vertical morphisms between the two
components of `y` lying over the comparison isomorphism of `y`, and two such morphisms have the
same image under `f`, so they agree by the faithfulness clause of Stacks 02ZY. -/
theorem subsingleton_representing_of_relativeDiagonal
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)) (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤
      (twoFibreProduct B S hS 𝒴 𝒳 𝒳 f.hom f.hom).val.obj)
    (hy : y ⋙ (twoFibreProduct B S hS 𝒴 𝒳 𝒳 f.hom f.hom).val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hE : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p
        (twoFibreProduct B S hS 𝒴 𝒳 𝒳 f.hom f.hom).val.p y
        (relativeDiagonalBasedFunctor B S hS 𝒳 𝒴 f.hom).toFunctor)
      (presheafOfCategories (F ⋙ typeToCat)).p)) :
    ∀ V, Subsingleton (F.obj V) := by
  have hfib : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  have hfaith := ((AlgebraicGeometry.isRepresentableByAlgebraicSpaces_iff_associatedMap B S hS f
    𝒴.val.p.chosenPullbacks).1 hf).1
  have hsubRel : ∀ a : BigFppfOver B U.left.1 U.left.2,
      Subsingleton (RelVertHom (Over.map U.hom) y a) := fun a =>
    subsingleton_relVertHom_of_faithful f.hom.w a (hfaith _)
  obtain ⟨iso⟩ := (nonempty_equivalenceOver_fst_iff 𝒴.isFiberedInGroupoids
    𝒳.isFiberedInGroupoids hy f.hom.w F).1 hE
  intro V
  have h1 : Subsingleton (RelVertHom (Over.map U.hom) y V.unop) := hsubRel V.unop
  have h2 : Subsingleton ((relVertHomPresheaf 𝒴.isFiberedInGroupoids 𝒳.isFiberedInGroupoids hy
      f.hom.w ⋙ uliftFunctor.{u, v}).obj V) :=
    (Equiv.ulift (α := RelVertHom (Over.map U.hom) y V.unop)).injective.subsingleton
  have hinj : Function.Injective (ConcreteCategory.hom (iso.inv.app V)) :=
    (ConcreteCategory.bijective_of_isIso (iso.inv.app V)).1
  have h3 : Subsingleton (ULift.{v, u} (F.obj V)) := hinj.subsingleton
  exact (Equiv.ulift.{v, u} (α := F.obj V)).symm.injective.subsingleton

/-- **Stacks 04YQ, part (3).** The relative diagonal of a 1-morphism of algebraic stacks over
the big fppf site of `S` which is representable by algebraic spaces is a monomorphism: it is
representable by algebraic spaces, and every algebraic space representing one of its base
changes along a scheme-valued point of `𝒳 ×_{f, 𝒴, f} 𝒳` has monomorphic structural morphism. -/
@[stacks 04YQ "part (3): monomorphism"]
theorem mono_relativeDiagonal_of_isRepresentableByAlgebraicSpaces
    {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) :
    ∃ _hΔ : IsRepresentableByAlgebraicSpaces B S hS
        (relativeDiagonalBasedFunctor B S hS 𝒳.val 𝒴.val f.hom.hom),
      ∀ (U : BigFppfOver B S hS)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤
          (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.obj)
        (_hy : y ⋙ (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p
          = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p
            (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p y
            (relativeDiagonalBasedFunctor B S hS 𝒳.val 𝒴.val f.hom.hom).toFunctor)
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        Mono (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)) := by
  refine ⟨isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f, ?_⟩
  intro U y hy F hF hE
  exact mono_algebraicSpaceMap_of_subsingleton B S hS U F hF
    (subsingleton_representing_of_relativeDiagonal B S hS 𝒳.val 𝒴.val f.hom hf U y hy F hE)

/-- **Stacks 04YQ, part (4).** The relative diagonal of a 1-morphism of algebraic stacks over
the big fppf site of `S` which is representable by algebraic spaces is separated: it is
representable by algebraic spaces, and every algebraic space representing one of its base
changes along a scheme-valued point of `𝒳 ×_{f, 𝒴, f} 𝒳` has separated structural morphism.

By part (3) that structural morphism is a monomorphism, and a monomorphism of algebraic spaces
is separated (Stacks 042N). -/
@[stacks 04YQ "part (4): separated"]
theorem isSeparated_relativeDiagonal_of_isRepresentableByAlgebraicSpaces
    {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) :
    ∃ _hΔ : IsRepresentableByAlgebraicSpaces B S hS
        (relativeDiagonalBasedFunctor B S hS 𝒳.val 𝒴.val f.hom.hom),
      ∀ (U : BigFppfOver B S hS)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤
          (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.obj)
        (_hy : y ⋙ (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p
          = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p
            (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p y
            (relativeDiagonalBasedFunctor B S hS 𝒳.val 𝒴.val f.hom.hom).toFunctor)
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        Space.IsSeparated B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom := by
  refine ⟨isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f, ?_⟩
  intro U y hy F hF hE
  exact Space.isSeparated_of_mono B S hS _
    (mono_hom_algebraicSpaceMap_of_subsingleton B S hS U F hF
      (subsingleton_representing_of_relativeDiagonal B S hS 𝒳.val 𝒴.val f.hom hf U y hy F hE))

end Stack

end AlgebraicGeometry

end
