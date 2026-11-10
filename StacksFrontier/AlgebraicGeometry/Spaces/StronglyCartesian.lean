module

public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace

/-!
# Strongly cartesian morphisms of algebraic spaces over varying bases (Stacks 04U9)

Let `S` be a scheme contained in a big fppf site `B`. The objects of the comma category of
Stacks 04U8 are pairs consisting of a scheme `T` over `S` and an algebraic space over `S`
equipped with a morphism to the presheaf of points of `T`; a morphism of such pairs is a map
of base schemes together with a map of the total algebraic spaces over it. Taking the base
scheme makes this a category over the big fppf site of `S`.

Stacks 04U9 identifies the strongly cartesian morphisms for that projection: a morphism is
strongly cartesian exactly when the square it forms is cartesian, i.e. when the canonical
comparison of its source with the fibre product of its target along the induced map of bases
is an isomorphism.

Both directions are a transcription of the universal properties. Given a strongly cartesian
morphism, the fibre product itself, with its first projection as structure map, is an object
over the same base, so the universal property produces a section of the comparison map over
the identity of the base; the cartesian square's own uniqueness makes it a two-sided inverse.
Conversely, if the comparison map is an isomorphism, a morphism into the target over a
factoring map of bases determines a map into the fibre product, hence into the source, and
the pullback square's uniqueness shows that map is the only lift.

## Main definitions

* `AlgebraicGeometry.spacesProjection`: the projection sending an algebraic space over a
  varying base scheme to that base scheme.

## Main results

* `AlgebraicGeometry.spacesProjection_isStronglyCartesian_iff`: **Stacks 04U9**.

## Implementation notes

The comma category is spelled out rather than abbreviated, so that it is the same expression
as in `AlgebraicGeometry.commaHomAsSpaceMap`, which carries the reading of an object's
structure map as a morphism of algebraic spaces. That helper is deliberately *not* used in
the statement or the proof: it is a plain `def`, so neither `rw` nor instance search unfolds
it, whereas the inline `CategoryTheory.ObjectProperty.homMk` of the structure map is what the
fibre product's universal property is phrased with.

The fibre product is the one in the category of algebraic spaces over `S`
(`AlgebraicGeometry.AlgebraicSpaces.fiberProduct`), whose cartesianness among algebraic
spaces is Stacks 02X2.

## References

* [Stacks Project, Tag 04U9](https://stacks.math.columbia.edu/tag/04U9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The projection from algebraic spaces over varying schemes to their bases. -/
abbrev spacesProjection (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⥤
      BigFppfOver B S hS :=
  Comma.snd _ _

/-- **Stacks 04U9.** A morphism of algebraic spaces over varying schemes is strongly
cartesian if and only if its canonical comparison with the base change of its target is an
isomorphism. -/
@[stacks 04U9]
theorem spacesProjection_isStronglyCartesian_iff
    {A C : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)} (m : A ⟶ C) :
    (spacesProjection B S hS).IsStronglyCartesian m.right m ↔
      IsIso (ObjectProperty.homMk (pullback.lift A.hom m.left.hom m.w.symm) :
        A.left ⟶ AlgebraicSpaces.fiberProduct B S hS
          (schemeSpaceMap m.right) (ObjectProperty.homMk C.hom)) := by
  let cMap : C.left ⟶ schemeSpace C.right := ObjectProperty.homMk C.hom
  let aMap : A.left ⟶ schemeSpace A.right := ObjectProperty.homMk A.hom
  let P := AlgebraicSpaces.fiberProduct B S hS (schemeSpaceMap m.right) cMap
  let fbase := (schemeSpaceMap m.right).hom
  let cbase := cMap.hom
  let p : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⥤
      BigFppfOver B S hS := Comma.snd _ _
  let e : A.left ⟶ P :=
    ObjectProperty.homMk (pullback.lift A.hom m.left.hom m.w.symm)
  let fstP : P ⟶ schemeSpace A.right :=
    ObjectProperty.homMk (pullback.fst fbase cbase)
  let sndP : P ⟶ C.left := ObjectProperty.homMk (pullback.snd fbase cbase)
  have hlift : ∀ {X Y : type_of% A} {g : X.right ⟶ Y.right} {φ : X ⟶ Y},
      p.IsHomLift g φ → φ.right = g := fun h => by
    simpa [p] using (IsHomLift.eq_of_isHomLift (p := p) (f := _) (φ := _)).symm
  have hpull := AlgebraicSpaces.isPullback_fiberProduct B S hS (schemeSpaceMap m.right) cMap
  have heFst : e ≫ fstP = aMap := ObjectProperty.hom_ext _ (pullback.lift_fst _ _ _)
  have heSnd : e ≫ sndP = m.left := ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _)
  constructor
  · intro hsc
    let Q : Comma
        (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
          IsAlgebraicSpace B S hS F))
        (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
      ⟨P, A.right, pullback.fst fbase cbase⟩
    let ψ : Q ⟶ C :=
      { left := ObjectProperty.homMk (pullback.snd fbase cbase)
        right := m.right
        w := by
          dsimp only [Q, schemeSpaceMap, fbase, cbase]
          exact pullback.condition.symm }
    have hψ : p.IsHomLift m.right ψ := Functor.IsHomLift.map (p := p) ψ
    have : p.IsHomLift (𝟙 A.right ≫ m.right) ψ := by simpa using hψ
    have : p.IsStronglyCartesian m.right m := hsc
    obtain ⟨χ, hχ, hχuniq⟩ :=
      Functor.IsStronglyCartesian.universal_property' (p := p) (f := m.right) (φ := m)
        (a' := Q) (𝟙 A.right) ψ
    have hχfac : χ ≫ m = ψ := hχ.2
    have hχright : χ.right = 𝟙 A.right := hlift hχ.1
    let s : P ⟶ A.left := ObjectProperty.homMk χ.left.hom
    have hw : s ≫ aMap = fstP := by
      apply ObjectProperty.hom_ext
      have hw' : χ.left.hom ≫ A.hom = Q.hom ≫ yoneda.map χ.right := χ.w
      rwa [hχright, yoneda.map_id, Category.comp_id] at hw'
    have hleft : s ≫ m.left = ψ.left := ObjectProperty.hom_ext _ <| by
      simpa [s] using congrArg (fun q : Q ⟶ C => q.left.hom) hχfac
    have hs_fst : s ≫ e ≫ fstP = fstP := by simp only [heFst, hw]
    have hs_snd : s ≫ e ≫ sndP = sndP := by
      simp only [heSnd, hleft]; rfl
    have hs_e : s ≫ e = 𝟙 P :=
      hpull.hom_ext (by simpa using hs_fst) (by simpa using hs_snd)
    have : IsIso e := ⟨⟨s, by
      let η : A ⟶ Q :=
        { left := e
          right := 𝟙 A.right
          w := by
            change e.hom ≫ fstP.hom = A.hom
            have h := congrArg (fun f => f.hom) heFst
            rw [ObjectProperty.FullSubcategory.comp_hom] at h
            simpa [aMap, schemeSpace] using h }
      have hηψ : η ≫ ψ = m := Comma.hom_ext _ _
        (ObjectProperty.hom_ext _ (by simpa [η, sndP, ψ] using congrArg (·.hom) heSnd)) rfl
      have hfac : (η ≫ χ) ≫ m = (𝟙 A) ≫ m := by
        simp only [Category.assoc, hχfac, hηψ, Category.id_comp]
      have hηχ : η ≫ χ = 𝟙 A := by
        have : p.IsHomLift (𝟙 A.right) (η ≫ χ) := by
          simpa [p, η, hχright] using Functor.IsHomLift.map (p := p) (η ≫ χ)
        have : p.IsHomLift (𝟙 A.right) (𝟙 A) := IsHomLift.id (p := p) rfl
        exact Functor.IsStronglyCartesian.ext (p := p) (f := m.right) (φ := m) (𝟙 A.right) hfac
      exact ObjectProperty.hom_ext _ <| by
        simpa [η, s] using congrArg (fun q : A ⟶ A => q.left.hom) hηχ, by simpa using hs_e⟩⟩
    infer_instance
  · intro he
    have : IsIso e := he
    have : p.IsHomLift m.right m := Functor.IsHomLift.map (p := p) m
    refine { universal_property' := ?_ }
    intro X g φ' hφ'
    have hbase : φ'.right = g ≫ m.right := hlift hφ'
    let betaRaw : X.left.obj ⟶ yoneda.obj A.right := X.hom ≫ yoneda.map g
    let beta : X.left.obj ⟶ (schemeSpace A.right).obj := by
      simpa [schemeSpace] using betaRaw
    have hcond : beta ≫ fbase = φ'.left.hom ≫ cbase := by
      have hcondRaw : betaRaw ≫ yoneda.map m.right = φ'.left.hom ≫ C.hom :=
        (Category.assoc _ _ _).trans <| by rw [← Functor.map_comp, ← hbase]; exact φ'.w.symm
      simpa [beta, betaRaw, fbase, cbase, cMap, schemeSpace, schemeSpaceMap] using hcondRaw
    let b : X.left ⟶ P := ObjectProperty.homMk (pullback.lift beta φ'.left.hom hcond)
    have hbFst : b ≫ fstP = ObjectProperty.homMk beta :=
      ObjectProperty.hom_ext _ (pullback.lift_fst _ _ _)
    have hbSnd : b ≫ sndP = φ'.left := ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _)
    have hinvFst : inv e ≫ aMap = fstP := by rw [← heFst, IsIso.inv_hom_id_assoc]
    have hinvSnd : inv e ≫ m.left = sndP := by rw [← heSnd, IsIso.inv_hom_id_assoc]
    let α : X.left ⟶ A.left := b ≫ inv e
    have hAlphaFst : α ≫ aMap = ObjectProperty.homMk beta := by
      simpa only [α, Category.assoc, hinvFst] using hbFst
    have hAlphaSnd : α ≫ m.left = φ'.left := by
      simpa only [α, Category.assoc, hinvSnd] using hbSnd
    let χ : X ⟶ A :=
      { left := α
        right := g
        w := by
          have h := congrArg (fun f => f.hom) hAlphaFst
          change α.hom ≫ A.hom = X.hom ≫ yoneda.map g
          simpa [aMap, beta, schemeSpace, schemeSpaceMap] using h }
    have hχlift : p.IsHomLift g χ := by
      have hmap : p.map χ = g := by simp [p, χ]
      exact hmap ▸ (Functor.IsHomLift.map χ)
    refine ⟨χ, ⟨hχlift, Comma.hom_ext _ _ hAlphaSnd hbase.symm⟩, ?_⟩
    intro χ' hχ'
    have hright : χ'.right = g := hlift hχ'.1
    have hleftfac : χ'.left ≫ m.left = φ'.left :=
      congrArg (fun q : X ⟶ C => q.left) hχ'.2
    have hfirstRaw : χ'.left.hom ≫ A.hom = betaRaw := by
      have hh : χ'.left.hom ≫ A.hom = X.hom ≫ yoneda.map χ'.right := χ'.w
      rwa [hright] at hh
    have hbfirstRaw : b.hom ≫ fstP.hom = betaRaw := by
      have hh := congrArg (fun f => f.hom) hbFst
      rw [ObjectProperty.FullSubcategory.comp_hom] at hh
      change b.hom ≫ fstP.hom = beta at hh
      simpa [beta, betaRaw, schemeSpace] using hh
    have hfirstBase : χ'.left ≫ aMap = b ≫ fstP :=
      ObjectProperty.hom_ext _ (hfirstRaw.trans hbfirstRaw.symm)
    have hfirst : (χ'.left ≫ e) ≫ fstP = b ≫ fstP := by
      simpa only [Category.assoc, heFst] using hfirstBase
    have hsecond : (χ'.left ≫ e) ≫ sndP = b ≫ sndP := by
      simpa only [Category.assoc, heSnd, hbSnd] using hleftfac
    have hcompare : χ'.left ≫ e = b := hpull.hom_ext hfirst hsecond
    have hleft : χ'.left = α := by
      simp [α, ← hcompare]
    exact Comma.hom_ext _ _ hleft (by simpa [χ] using hright)

end AlgebraicGeometry

end
