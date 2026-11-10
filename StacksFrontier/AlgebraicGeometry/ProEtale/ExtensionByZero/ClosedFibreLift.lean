module

public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtale.JacobsonQuotientRetraction
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.AffineIndEtaleAdjunction

/-!
# The final object of the affine ind-étale site and its lift along a closed immersion

For an affine object `S` of a big pro-étale site, the identity `S/S` is an object of the affine
ind-étale pro-étale site of `S`, and it is the final object there.

Let `i : Z ⟶ X` be a closed immersion of affine objects of the site, with `I ⊆ Γ(X, ⊤)` the
ideal cutting out `Z`. If `Γ(X, ⊤)` is w-contractible and `I` lies in its Jacobson radical, then
the lift of the final object of the site of `Z` along `i` is the final object of the site of
`X`.

## Main definitions

* `AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.terminalObj`: the identity of `S`, as an
  object of the affine ind-étale pro-étale site of `S`.

## Main results

* `AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.terminalObj_isTerminal`: the identity of
  `S` is the final object of the affine ind-étale pro-étale site of `S`.
* `AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.affineIndEtaleLift_obj_terminalObj_iso`:
  the lift along a closed immersion carries the final object to the final object.

## References

* [Stacks Project, Tag 09AC](https://stacks.math.columbia.edu/tag/09AC)
* [Stacks Project, Tag 09BK](https://stacks.math.columbia.edu/tag/09BK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.ProEtale

/-- The map on global sections of the identity of an object of a big pro-étale site is the
identity. -/
lemma inclusion_map_id_appTop (B : BigProetaleSite.{u}) (S : B.Scheme) :
    (B.inclusion.map (𝟙 S)).appTop = 𝟙 Γ(S.obj, ⊤) := by
  rw [CategoryTheory.Functor.map_id, Scheme.Hom.id_appTop]
  rfl

namespace AffineIndEtaleProetale

/-- The identity of `S`, the final object of the small pro-étale site of `S`, as an object of
the affine ind-étale pro-étale site of `S`. -/
def terminalObj (B : BigProetaleSite.{u}) (S : B.Scheme) [IsAffine S.obj] :
    AffineIndEtaleProetale B S :=
  ⟨smallIdentity B S.obj S.property, ‹IsAffine S.obj›, by
    rw [show (B.inclusion.map (smallIdentity B S.obj S.property).obj.hom).appTop =
        𝟙 Γ(S.obj, ⊤) from inclusion_map_id_appTop B _]
    exact ObjectProperty.le_ind _ _ (RingHom.Etale.of_bijective Function.bijective_id)⟩

/-- The underlying object of the small pro-étale site of the final object of the affine
ind-étale pro-étale site of `S` is the identity of `S`. -/
lemma inclusion_obj_terminalObj (B : BigProetaleSite.{u}) (S : B.Scheme) [IsAffine S.obj] :
    (inclusion B S).obj (terminalObj B S) = smallIdentity B S.obj S.property :=
  rfl

/-- The identity of `S` is the final object of the affine ind-étale pro-étale site of `S`. -/
def terminalObj_isTerminal (B : BigProetaleSite.{u}) (S : B.Scheme) [IsAffine S.obj] :
    IsTerminal (terminalObj B S) :=
  IsTerminal.ofUniqueHom
    (fun _ ↦ (inclusion B S).preimage ((smallIdentity_isTerminal B S.obj S.property).from _))
    fun _ _ ↦ (inclusion B S).map_injective
      ((smallIdentity_isTerminal B S.obj S.property).hom_ext _ _)

end AffineIndEtaleProetale

/-- Rebasing `R`, as an ind-étale algebra over itself, along an isomorphism `e : A ≅ R` of base
rings gives `A` as an ind-étale algebra over itself. -/
def rebaseIndEtaleAlongIso_obj_indEtaleAlgebraSelf {A R : Type u} [CommRing A] [CommRing R]
    (e : CommRingCat.of A ≅ CommRingCat.of R) :
    indEtaleAlgebraSelf A ≅
      ((rebaseIndEtaleAlongIso e).obj (op (indEtaleAlgebraSelf R))).unop :=
  ObjectProperty.isoMk _ (Under.isoMk e (by
    change 𝟙 (CommRingCat.of A) ≫ e.hom = e.hom ≫ 𝟙 (CommRingCat.of R)
    simp))

/-- The global sections of the final object of the affine ind-étale pro-étale site of `S` are
`Γ(S, ⊤)`, as an ind-étale algebra over itself. -/
lemma globalSections_obj_terminalObj (B : BigProetaleSite.{u}) (S : B.Scheme)
    [IsAffine S.obj] :
    (affineIndEtaleGlobalSections B S).obj (AffineIndEtaleProetale.terminalObj B S) =
      op (indEtaleAlgebraSelf Γ(S.obj, ⊤)) := by
  refine congrArg op (ObjectProperty.FullSubcategory.ext ?_)
  change Under.mk (B.inclusion.map (𝟙 (⟨S.obj, S.property⟩ : B.Scheme))).appTop =
    Under.mk (𝟙 (CommRingCat.of Γ(S.obj, ⊤)))
  rw [inclusion_map_id_appTop]
  rfl

namespace AffineIndEtaleProetale

/-- Let `i : Z ⟶ X` be a closed immersion of affine objects of a big pro-étale site, with `I` the
ideal of `Γ(X, ⊤)` cutting out `Z`. If `Γ(X, ⊤)` is w-contractible and `I` is contained in its
Jacobson radical, then the lift along `i` carries the final object of the affine ind-étale
pro-étale site of `Z` to the final object of that of `X`. -/
def affineIndEtaleLift_obj_terminalObj_iso (B : BigProetaleSite.{u}) {Z X : B.Scheme}
    (i : Z ⟶ X) [IsAffine X.obj] [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)]
    (hA : ProetaleWContractible.IsWContractible.{u, u} Γ(X.obj, ⊤))
    (hI : (affineClosedImmersionRingData B i).1 ≤ Ring.jacobson Γ(X.obj, ⊤)) :
    (affineIndEtaleLift B i).obj (terminalObj B Z) ≅ terminalObj B X := by
  refine (affineIndEtaleGlobalSections_fullyFaithful B X).preimageIso
    ((affineIndEtaleLiftGlobalSectionsIso B i (terminalObj B Z)).symm.op ≪≫ ?_)
  refine (rebaseIndEtaleAlongIso (affineClosedImmersionRingData B i).2 ⋙
      (indEtaleQuotientLift Γ(X.obj, ⊤) (affineClosedImmersionRingData B i).1).op).mapIso
    (eqToIso (globalSections_obj_terminalObj B Z)) ≪≫ ?_
  refine (indEtaleQuotientLift Γ(X.obj, ⊤) (affineClosedImmersionRingData B i).1).op.mapIso
    (rebaseIndEtaleAlongIso_obj_indEtaleAlgebraSelf
      (affineClosedImmersionRingData B i).2).op ≪≫ ?_
  exact (indEtaleQuotientLift_self_iso Γ(X.obj, ⊤) hA
      (affineClosedImmersionRingData B i).1 hI).some.op ≪≫
    eqToIso (globalSections_obj_terminalObj B X).symm

end AffineIndEtaleProetale

end AlgebraicGeometry.ProEtale

end
