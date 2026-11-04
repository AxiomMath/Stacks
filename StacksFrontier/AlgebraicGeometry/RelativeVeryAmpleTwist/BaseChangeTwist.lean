module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleBaseChangeTwist
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.DegreeOne
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Relative very ampleness under base change

Let `f : X ⟶ S` be a morphism of schemes, `L` an invertible `𝒪_X`-module which is very ample
relative to `f` in the sense of [Stacks, Tag 01VM], and `g : S' ⟶ S` a morphism of schemes. Then
the pullback of `L` to `S' ×_S X` is very ample relative to the projection `S' ×_S X ⟶ S'`
[Stacks, Tag 0B3F]. The input is the base change of the projective bundle together with its twist:
for a quasi-coherent `𝒪_S`-module `E` and a quasi-coherent `𝒪_{S'}`-module `E'` identified with
`g^* E`, the projective bundle `𝐏(E')` is the fibre product `S' ×_S 𝐏(E)` and the comparison
morphism `b : 𝐏(E') ⟶ 𝐏(E)` pulls `𝒪_{𝐏(E)}(1)` back to `𝒪_{𝐏(E')}(1)`, which is
[Stacks, Tag 01O3] for the symmetric algebra, in degree one. As a consequence relative very
ampleness restricts to every open of the base.

## Main results

* `Stacks.Tag01VMVeryAmple.projectiveBundleTwistBaseChange`: **Tag 01O3 for `Sym(E)` in degree
  one**, with the twist `Stacks.Tag01VMVeryAmple.twistOne` of Tag 01VM.
* `Stacks.Tag01VMVeryAmple.isRelativelyVeryAmple_pullback_fst`: **Stacks Tag 0B3F.**
* `Stacks.Tag01VMVeryAmple.isRelativelyVeryAmple_morphismRestrict`: **relative very ampleness
  restricts to an open of the base.** If `L` is very ample relative to `f : X ⟶ S` then for every
  open `V ⊆ S` the restriction `L|_{f⁻¹(V)}` is very ample relative to `f ∣_ V : f⁻¹(V) ⟶ V`.

## Implementation notes

**The comparison morphism is `Stacks.ProjectiveBundle.baseChangeHom`.** It is cartesian over `g`
by `Stacks.ProjectiveBundle.isPullback_baseChangeHom`, and over a covering of `S'` by affine charts
it is `Proj` of a graded ring map sending the degree-one generator attached to a section of `E` to
the one attached to its pullback (`Stacks.ProjectiveBundle.exists_chart_baseChangeHom`), which is
the input of `Stacks.Chow.GenuineChern.twistPullbackIso`. The twist that lemma is about,
`Stacks.ProjectiveBundleSplitting.tautologicalTwist`, is the degree-one piece of the glued twist
algebra of `Sym(E)`; `Stacks.Tag01VMVeryAmple.twistOne` is the glued degree-one twist of `Sym(E)`.
The two are the same module: the glued twist algebra has the glued twists as its pieces on the
nose, and the cocycle conditions indexing them are propositions.

**The route of Tag 0B3F.** The source's three steps are followed exactly. The immersion over the
new base is `CategoryTheory.IsPullback.lift` of `S' ×_S X ⟶ X ⟶ 𝐏(E)` and `S' ×_S X ⟶ S'`
against the cartesian square `𝐏(g^* E) = S' ×_S 𝐏(E)`; that it is an immersion is Tag 01JY,
`AlgebraicGeometry.IsImmersion.isStableUnderBaseChange`, applied to the square
`CategoryTheory.IsPullback.of_bot'` produces out of the fibre-product square of `g` and `f`
divided by the square of `g` and the projection of `𝐏(E)`. The comparison of the pulled-back
module is the chain
`(p_X)^* i^* 𝒪(1) ≅ (i ∘ p_X)^* 𝒪(1) = (b ∘ i')^* 𝒪(1) ≅ i'^* b^* 𝒪(1) ≅ i'^* 𝒪_{𝐏(g^* E)}(1)`.
Quasi-coherence of `g^* E` (Tag 01BG) is supplied to
`AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent` explicitly, at the ringed-space
spelling that lemma is stated at.

**The restriction is the base change along `V.ι`.** Tag 0B3F applied to the inclusion of `V`
gives very ampleness for the projection `V ×_S X ⟶ V`, and
`AlgebraicGeometry.pullbackRestrictIsoRestrict` identifies that projection with `f ∣_ V`, so
`Stacks.Tag01VMVeryAmple.isRelativelyVeryAmple_of_isIso` carries it across.

## References

* [Stacks Project, Tag 0B3F](https://stacks.math.columbia.edu/tag/0B3F)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 01JY](https://stacks.math.columbia.edu/tag/01JY)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Ample
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.Tag01VMRelativeVeryAmple

universe u

namespace Stacks.Tag01VMVeryAmple

/-- **Stacks Tag 01O3 for the sheaf symmetric algebra, in degree one.** For `g : S' ⟶ S`, a
quasi-coherent `E` on `S` and a quasi-coherent `E'` on `S'` identified with `g^* E`, there is a
morphism `b : 𝐏(E') ⟶ 𝐏(E)` exhibiting `𝐏(E')` as the fibre product `S' ×_S 𝐏(E)` and pulling
`𝒪_{𝐏(E)}(1)` back to `𝒪_{𝐏(E')}(1)`. -/
theorem projectiveBundleTwistBaseChange {S S' : Scheme.{u}} (g : S' ⟶ S) (E : S.Modules)
    [E.IsQuasicoherent] (E' : S'.Modules) [E'.IsQuasicoherent]
    (hE : E' ≅ (Scheme.Modules.pullback g).obj E) :
    ∃ b : (relativeProj (symAlgebra E')).scheme ⟶ (relativeProj (symAlgebra E)).scheme,
      IsPullback (relativeProj (symAlgebra E')).toBase b g
          (relativeProj (symAlgebra E)).toBase ∧
        Nonempty ((Scheme.Modules.pullback b).obj (twistOne E) ≅ twistOne E') := by
  have hpb := Stacks.ProjectiveBundle.isPullback_baseChangeHom g E
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E) E'
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E') hE
  exact ⟨_, hpb, ⟨Stacks.Chow.GenuineChern.twistPullbackIso g
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E)
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E') hE.inv _ hpb.w.symm
    (Stacks.ProjectiveBundle.exists_chart_baseChangeHom g E _ E' _ hE)⟩⟩

variable {S : Scheme.{u}}

/-- **Stacks Tag 0B3F: relative very ampleness is preserved by base change.** Let `f : X ⟶ S` be
a morphism of schemes, `L` an invertible `𝒪_X`-module which is very ample relative to `f`, and
`g : S' ⟶ S` a morphism of schemes. Then the pullback of `L` to `S' ×_S X` is very ample relative
to the projection `S' ×_S X ⟶ S'`.

The proof is the source's. Relative very ampleness gives a quasi-coherent `𝒪_S`-module `E`, an
immersion `i : X ⟶ 𝐏(E)` over `S` and an isomorphism `L ≅ i^* 𝒪_{𝐏(E)}(1)`. The module `g^* E` is
quasi-coherent (Tag 01BG), its projective bundle is the base change of `𝐏(E)` and the comparison
morphism `b` pulls the twist back to the twist (Tag 01O3,
`Stacks.Tag01VMVeryAmple.projectiveBundleTwistBaseChange`), so the morphism `i'` induced by
`S' ×_S X ⟶ X ⟶ 𝐏(E)` and `S' ×_S X ⟶ S'` is a base change of `i`, hence an immersion
(Tag 01JY), it lies over `S'`, and the pullback of `L` is `i'^* 𝒪_{𝐏(g^* E)}(1)`. -/
@[stacks 0B3F, ega "II 4.4.10", sga "1 VIII 5.8" "Very ample clause"]
theorem isRelativelyVeryAmple_pullback_fst {X S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] (hL : IsRelativelyVeryAmple f L) :
    IsRelativelyVeryAmple (pullback.fst g f)
      ((Scheme.Modules.pullback (pullback.snd g f)).obj L) := by
  obtain ⟨E, hE, i, him, hover, ⟨e⟩⟩ := hL
  have : E.IsQuasicoherent := hE
  have : ((Scheme.Modules.pullback g).obj E).IsQuasicoherent :=
    @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent S'.toRingedSpace
      S.toRingedSpace g.toLRSHom.toShHom E hE
  obtain ⟨b, hsq, ⟨tw⟩⟩ :=
    projectiveBundleTwistBaseChange g E ((Scheme.Modules.pullback g).obj E) (Iso.refl _)
  have hs : IsPullback (pullback.snd g f) (pullback.fst g f)
      (i ≫ (relativeProj (symAlgebra E)).toBase) g := by
    rw [hover]
    exact (IsPullback.of_hasPullback g f).flip
  have hsqfinal := hs.of_bot' hsq.flip
  set i' := hsq.flip.lift (pullback.snd g f ≫ i) (pullback.fst g f)
    (by rw [Category.assoc, hs.w])
  have hfst : i' ≫ b = pullback.snd g f ≫ i := hsq.flip.lift_fst _ _ _
  have hsnd : i' ≫ (relativeProj
      (symAlgebra ((Scheme.Modules.pullback g).obj E))).toBase = pullback.fst g f :=
    hsq.flip.lift_snd _ _ _
  have himm : IsImmersion i' :=
    IsImmersion.isStableUnderBaseChange.of_isPullback hsqfinal him
  have eL : (Scheme.Modules.pullback (pullback.snd g f)).obj L ≅
      (Scheme.Modules.pullback i').obj (twistOne ((Scheme.Modules.pullback g).obj E)) :=
    (Scheme.Modules.pullback (pullback.snd g f)).mapIso e ≪≫
      (Scheme.Modules.pullbackComp (pullback.snd g f) i).app (twistOne E) ≪≫
      (Scheme.Modules.pullbackCongr hfst.symm).app (twistOne E) ≪≫
      ((Scheme.Modules.pullbackComp i' b).app (twistOne E)).symm ≪≫
      (Scheme.Modules.pullback i').mapIso tw
  exact isRelativelyVeryAmple_of_immersion _ _ ((Scheme.Modules.pullback g).obj E) i'
    himm hsnd eL

/-- **Relative very ampleness restricts to an open of the base.** If `L` is very ample relative
to `f : X ⟶ S`, then for every open `V ⊆ S` the restriction of `L` to `f⁻¹(V)` is very ample
relative to `f ∣_ V : f⁻¹(V) ⟶ V`.

It is the base change of `f` along the inclusion of `V` (Stacks Tag 0B3F), read through the
identification of `V ×_S X` with `f⁻¹(V)`. -/
@[ega "II 4.4.10" "(iii), special case"]
theorem isRelativelyVeryAmple_morphismRestrict {X : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] (hL : IsRelativelyVeryAmple f L) (V : S.Opens) :
    IsRelativelyVeryAmple (f ∣_ V) ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L) := by
  have h := isRelativelyVeryAmple_pullback_fst f V.ι L hL
  let p : (f ⁻¹ᵁ V).toScheme ⟶ pullback V.ι f :=
    (pullbackRestrictIsoRestrict f V).inv ≫ (pullbackSymmetry f V.ι).hom
  have hp₁ : p ≫ pullback.fst V.ι f = f ∣_ V := by
    simp only [p, Category.assoc, pullbackSymmetry_hom_comp_fst,
      Iso.inv_comp_eq, pullbackRestrictIsoRestrict_hom_morphismRestrict]
  have hp₂ : p ≫ pullback.snd V.ι f = (f ⁻¹ᵁ V).ι := by
    simp only [p, Category.assoc, pullbackSymmetry_hom_comp_snd,
      pullbackRestrictIsoRestrict_inv_fst]
  have e : (modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L ≅
      (Scheme.Modules.pullback p).obj
        ((Scheme.Modules.pullback (pullback.snd V.ι f)).obj L) :=
    (Scheme.Modules.pullbackCongr hp₂.symm).app L ≪≫
      ((Scheme.Modules.pullbackComp p (pullback.snd V.ι f)).app L).symm
  have h' := isRelativelyVeryAmple_of_isIso p (pullback.fst V.ι f) _ _ e h
  rwa [hp₁] at h'

end Stacks.Tag01VMVeryAmple

end
