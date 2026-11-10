module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageRestrictScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsCompIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FSharpCommRingCompositionLaw
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqTranspose

/-!
# The composition law for step 5 of the chain of Tag 03EL

`Stacks.SheafOfModules.pullbackTensorStep5` is the fifth link of the chain of bijections of
Tag 03EL, the extension-restriction adjunction of Stacks 03CZ:

`Hom_{χ⁻¹O_E}(χ⁻¹F ⊗ χ⁻¹G, N|) = Hom_{O_C}(O_C ⊗_{χ⁻¹O_E} (χ⁻¹F ⊗ χ⁻¹G), N)`.

The morphism of ringed topoi `χ` enters it only through the comm-ring form `χ♯ : χ⁻¹O_E ⟶ O_C` of
its structure map, so the composition law for step 5 is the composition law for that one
morphism, `Stacks.Sheaves.RingedToposModules.fSharpCommRing_comp`, read through the adjunction.
That law exhibits `(ψ ∘ φ)♯` as a *threefold* composite

`(ψ ∘ φ)⁻¹O_E ⟶ φ⁻¹(ψ⁻¹O_E) ⟶ φ⁻¹O_D ⟶ O_C`,

so extension of scalars along it is the threefold composite of extensions of scalars — two
applications of `Stacks.Sheaves.RingedToposModules.extendScalarsCompIso` — and the inverse
transpose across the one adjunction is the three inverse transposes taken in turn.

## Main definitions

* `Stacks.SheafOfModules.step5CompMid`: the intermediate presheaf of commutative rings
  `φ⁻¹(ψ⁻¹O_E)` of the factorisation.
* `Stacks.SheafOfModules.step5CompFactor₁`, `…₂`, `…₃`: the three factors.
* `Stacks.SheafOfModules.step5CompTensor`: the tensor product of the two inverse images over
  `(ψ ∘ φ)⁻¹O_E`, the object step 5 for the composite is a bijection of morphisms out of.

## Main results

* `Stacks.SheafOfModules.restrictScalars_commRingSheafMap_eq_comp₃`: restriction of scalars along
  a threefold-factored morphism of presheaves of commutative rings is restriction along the three
  factors in turn.
* `Stacks.SheafOfModules.isSheaf_step5CompMid`: the sheaf condition for the intermediate presheaf
  of commutative rings the factorisation passes through. It is the sheaf condition of the
  corresponding sheaf of commutative rings, read on its underlying presheaf of rings.
* `Stacks.SheafOfModules.step5CompExtendEq` and `Stacks.SheafOfModules.step5CompValuesEq`: the two
  transports along the factorisation that the law needs — of the source object of step 5, and of
  its sheaf of values.
* `Stacks.SheafOfModules.pullbackTensorStep5_comp`: **the composition law for step 5.**

## Implementation notes

*The three factors.* They are literally the three factors of
`Stacks.Sheaves.RingedToposModules.fSharpCommRing_comp`: the comparison of the inverse image
along the composite with the iterated inverse image, the inverse image along `φ` of the comm-ring
form of `ψ♯` (in the `⟨…⟩` reading of it that
`Stacks.Sheaves.RingedToposModules.mk_fSharpCommRing_eq_fSharpInverseImage` identifies with
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage`), and the comm-ring form of `φ♯`. Only the
third has extension of scalars along it already named: it is
`Stacks.Sheaves.RingedToposModules.extendScalarsFSharp` of `φ`, so the outermost of the three
inverse transposes is taken in the very adjunction that step 5 for `φ` is.

*Why the transports are written out.* `fSharpCommRing_comp` is not definitional, so the object
`(extendScalarsFSharp (ψ ∘ φ)).obj T` that step 5 for the composite maps out of and the object
`(extendScalars (θ₁ ≫ θ₂ ≫ θ₃)).obj T` that the comparison isomorphisms are stated at are equal
only propositionally. The merge of the three restrictions of scalars into one *is* definitional,
but no consumer can afford to leave it so: asking the elaborator to identify
`N|_{(ψ ∘ φ)⁻¹O_E}` with `((N|_{φ⁻¹O_D})|_{φ⁻¹(ψ⁻¹O_E)})|_{(ψ ∘ φ)⁻¹O_E}` at these concrete
morphisms of sheaves of rings is a deterministic 200000-heartbeat `whnf` timeout. Both transports
are therefore `CategoryTheory.eqToHom` of a named
equation — `Stacks.SheafOfModules.step5CompExtendEq` and
`Stacks.SheafOfModules.step5CompValuesEq` — whose own proofs do the identification once, the
second of them through `Stacks.Sheaves.RingedToposModules.restrictScalars_comp`, which is generic
in the two morphisms of sheaves of rings and so costs nothing.

*Why no `rw`.* Rewriting `fSharpCommRing_comp` in place asks the elaborator to rewrite across the
seam between a sheaf of commutative rings and its underlying sheaf of rings, which reports a
target that is not type-correct at the ambient transparency. The content is therefore packaged as
private lemmas over an abstract site and abstract morphisms of abstract presheaves of commutative
rings, with the factorisation as a *hypothesis* on a variable, and applied by `exact`. The two
transports enter those lemmas as opaque hypotheses for the same reason.

*The normalisation of `extendScalarsCompIso`.* It is a bare
`CategoryTheory.Adjunction.leftAdjointUniq`, and what an inverse transpose does to that is
`CategoryTheory.Adjunction.leftAdjointUniq_hom_app_comp_homEquiv_symm''`, already available. The
only thing added here is the form with the comparison left opaque — supplied as an isomorphism
together with the equation identifying it — which is how
`StacksFrontier/CategoryTheory/Adjunction/LeftAdjointUniqTranspose.lean` records that a consumer
with concrete adjoints has to use these identities.

**Universes.** The three ringed topoi share the universe `w` of the sections of their structure
sheaves. That is inherited, not chosen: `fSharpCommRing_comp` requires it, and through it
`Stacks.Sheaves.ToposPullback.pullbackCommRingSheafFunctorComp`, which takes the sheaves of
commutative rings of its three sites in one universe. The object and morphism universes of the
three sites stay independent. The composition laws for steps 2 and 3 of the chain need no such
comparison and are stated at three independent section universes.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.SheafOfModules

universe w v u v' u' v'' u''

section Transpose

/-- **The inverse transpose across one of two adjunctions with the same right adjoint, with the
comparison of the two left adjoints left opaque**: it is supplied as an isomorphism `e` together
with the equation identifying it with `CategoryTheory.Adjunction.leftAdjointUniq`.

This is `CategoryTheory.Adjunction.leftAdjointUniq_hom_app_comp_homEquiv_symm''`, and it exists in
this form for the reason the implementation notes of
`StacksFrontier/CategoryTheory/Adjunction/LeftAdjointUniqTranspose.lean` record: at concrete
adjunctions, writing `…leftAdjointUniq` where the elaborator must match it against an expected
type forces the comparison to be reduced to a structure. With `e` a variable nothing reduces, and
the consumer supplies the equation separately as a `rfl` against its own definition. -/
private theorem homEquiv_symm_of_eq_leftAdjointUniq {D : Type u} [Category.{v} D] {E : Type u'}
    [Category.{v'} E] {L L' : D ⥤ E} {R : E ⥤ D} (adj1 : L ⊣ R) (adj2 : L' ⊣ R) (e : L ≅ L')
    (he : e = Adjunction.leftAdjointUniq adj1 adj2) {x : D} {y : E} (t : x ⟶ R.obj y) :
    (adj1.homEquiv x y).symm t = e.hom.app x ≫ (adj2.homEquiv x y).symm t := by
  subst he
  exact (Adjunction.leftAdjointUniq_hom_app_comp_homEquiv_symm'' adj1 adj2 t).symm

end Transpose

section ExtendScalarsTranspose

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A₁ A₂ A₃ A₄ : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- Restricting scalars along a composite of two morphisms of presheaves of commutative rings is
restricting along the two factors in turn, on one object.

Stated over abstract morphisms, where it is
`Stacks.Sheaves.RingedToposModules.restrictScalars_comp` and costs nothing; at the comm-ring
forms of two structure maps the same identification is a `whnf` timeout. -/
private theorem restrictScalars_commRingSheafMap_comp_obj (θ₁ : A₁ ⟶ A₂) (θ₂ : A₂ ⟶ A₃)
    (h₁ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₁))
    (h₂ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₂))
    (h₃ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₃))
    (M : SheafOfModules.{w} (commRingSheaf J A₃ h₃)) :
    (SheafOfModules.restrictScalars (commRingSheafMap J (θ₁ ≫ θ₂) h₁ h₃)).obj M =
      (SheafOfModules.restrictScalars (commRingSheafMap J θ₁ h₁ h₂)).obj
        ((SheafOfModules.restrictScalars (commRingSheafMap J θ₂ h₂ h₃)).obj M) :=
  (congrArg
    (fun F : SheafOfModules.{w} (commRingSheaf J A₃ h₃) ⥤
        SheafOfModules.{w} (commRingSheaf J A₁ h₁) ↦ F.obj M)
    (Stacks.Sheaves.RingedToposModules.restrictScalars_comp
      (commRingSheafMap J θ₁ h₁ h₂) (commRingSheafMap J θ₂ h₂ h₃))).symm

/-- **Restricting scalars along a threefold-factored morphism of presheaves of commutative rings
is restricting along the three factors in turn**, on one object. -/
theorem restrictScalars_commRingSheafMap_eq_comp₃ (θ : A₁ ⟶ A₄) (θ₁ : A₁ ⟶ A₂) (θ₂ : A₂ ⟶ A₃)
    (θ₃ : A₃ ⟶ A₄) (hθ : θ = θ₁ ≫ θ₂ ≫ θ₃)
    (h₁ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₁))
    (h₂ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₂))
    (h₃ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₃))
    (h₄ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₄))
    (M : SheafOfModules.{w} (commRingSheaf J A₄ h₄)) :
    (SheafOfModules.restrictScalars (commRingSheafMap J θ h₁ h₄)).obj M =
      (SheafOfModules.restrictScalars (commRingSheafMap J θ₁ h₁ h₂)).obj
        ((SheafOfModules.restrictScalars (commRingSheafMap J θ₂ h₂ h₃)).obj
          ((SheafOfModules.restrictScalars (commRingSheafMap J θ₃ h₃ h₄)).obj M)) := by
  subst hθ
  exact (restrictScalars_commRingSheafMap_comp_obj J θ₁ (θ₂ ≫ θ₃) h₁ h₂ h₄ M).trans
    (congrArg
      (fun P : SheafOfModules.{w} (commRingSheaf J A₂ h₂) ↦
        (SheafOfModules.restrictScalars (commRingSheafMap J θ₁ h₁ h₂)).obj P)
      (restrictScalars_commRingSheafMap_comp_obj J θ₂ θ₃ h₂ h₃ h₄ M))

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The inverse transpose of a morphism across the extension-restriction adjunction along a
composite is the comparison of the two extensions of scalars followed by the two inverse
transposes taken in turn.

Stated over abstract morphisms of abstract presheaves of commutative rings on an abstract site:
every use of it is at a comm-ring form of a structure map, where rewriting in place reports a
target that is not type-correct at the ambient transparency. -/
private theorem extendScalars_homEquiv_symm_comp (θ₁ : A₁ ⟶ A₂) (θ₂ : A₂ ⟶ A₃)
    (h₁ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₁))
    (h₂ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₂))
    (h₃ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₃))
    (T : SheafOfModules.{w} (commRingSheaf J A₁ h₁))
    (M : SheafOfModules.{w} (commRingSheaf J A₃ h₃))
    (g : T ⟶ (SheafOfModules.restrictScalars (commRingSheafMap J (θ₁ ≫ θ₂) h₁ h₃)).obj M) :
    ((extendRestrictScalarsAdjunction J (θ₁ ≫ θ₂) h₁ h₃).homEquiv T M).symm g =
      (extendScalarsCompIso J θ₁ θ₂ h₁ h₂ h₃).hom.app T ≫
        ((extendRestrictScalarsAdjunction J θ₂ h₂ h₃).homEquiv
            ((extendScalars J θ₁ h₁ h₂).obj T) M).symm
          (((extendRestrictScalarsAdjunction J θ₁ h₁ h₂).homEquiv T
            ((SheafOfModules.restrictScalars (commRingSheafMap J θ₂ h₂ h₃)).obj M)).symm g) := by
  refine (homEquiv_symm_of_eq_leftAdjointUniq
    (extendRestrictScalarsAdjunction J (θ₁ ≫ θ₂) h₁ h₃)
    ((extendRestrictScalarsAdjunction J θ₁ h₁ h₂).comp
      (extendRestrictScalarsAdjunction J θ₂ h₂ h₃))
    (extendScalarsCompIso J θ₁ θ₂ h₁ h₂ h₃) rfl g).trans
      (congrArg (fun m ↦ (extendScalarsCompIso J θ₁ θ₂ h₁ h₂ h₃).hom.app T ≫ m) ?_)
  exact congrArg (fun k ↦ (k T M).symm g)
    (Adjunction.comp_homEquiv (extendRestrictScalarsAdjunction J θ₁ h₁ h₂)
      (extendRestrictScalarsAdjunction J θ₂ h₂ h₃))

/-- The inverse transpose of a morphism across the extension-restriction adjunction along a
morphism of presheaves of commutative rings presented as a *threefold* composite: the two
comparisons of extensions of scalars followed by the three inverse transposes taken in turn.

The factorisation is a hypothesis on a variable morphism, so that `subst` is available and no
rewriting across a ring-sheaf seam is performed; the two transports it forces are hypotheses too,
so that a consumer may supply them in whatever spelling its own statement needs. -/
private theorem extendScalars_homEquiv_symm_comp₃ (θ : A₁ ⟶ A₄) (θ₁ : A₁ ⟶ A₂) (θ₂ : A₂ ⟶ A₃)
    (θ₃ : A₃ ⟶ A₄) (hθ : θ = θ₁ ≫ θ₂ ≫ θ₃)
    (h₁ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₁))
    (h₂ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₂))
    (h₃ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₃))
    (h₄ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₄))
    (T : SheafOfModules.{w} (commRingSheaf J A₁ h₁))
    (M : SheafOfModules.{w} (commRingSheaf J A₄ h₄))
    (eT : (extendScalars J θ h₁ h₄).obj T = (extendScalars J (θ₁ ≫ θ₂ ≫ θ₃) h₁ h₄).obj T)
    (eM : (SheafOfModules.restrictScalars (commRingSheafMap J θ h₁ h₄)).obj M =
      (SheafOfModules.restrictScalars (commRingSheafMap J θ₁ h₁ h₂)).obj
        ((SheafOfModules.restrictScalars (commRingSheafMap J θ₂ h₂ h₃)).obj
          ((SheafOfModules.restrictScalars (commRingSheafMap J θ₃ h₃ h₄)).obj M)))
    (g : T ⟶ (SheafOfModules.restrictScalars (commRingSheafMap J θ h₁ h₄)).obj M) :
    ((extendRestrictScalarsAdjunction J θ h₁ h₄).homEquiv T M).symm g =
      eqToHom eT ≫ (extendScalarsCompIso J θ₁ (θ₂ ≫ θ₃) h₁ h₂ h₄).hom.app T ≫
        (extendScalarsCompIso J θ₂ θ₃ h₂ h₃ h₄).hom.app ((extendScalars J θ₁ h₁ h₂).obj T) ≫
          ((extendRestrictScalarsAdjunction J θ₃ h₃ h₄).homEquiv
              ((extendScalars J θ₂ h₂ h₃).obj ((extendScalars J θ₁ h₁ h₂).obj T)) M).symm
            (((extendRestrictScalarsAdjunction J θ₂ h₂ h₃).homEquiv
                ((extendScalars J θ₁ h₁ h₂).obj T)
                ((SheafOfModules.restrictScalars (commRingSheafMap J θ₃ h₃ h₄)).obj M)).symm
              (((extendRestrictScalarsAdjunction J θ₁ h₁ h₂).homEquiv T
                  ((SheafOfModules.restrictScalars (commRingSheafMap J θ₂ h₂ h₃)).obj
                    ((SheafOfModules.restrictScalars
                      (commRingSheafMap J θ₃ h₃ h₄)).obj M))).symm (g ≫ eqToHom eM))) := by
  subst hθ
  have hM : g ≫ eqToHom eM = g :=
    (congrArg (fun m ↦ g ≫ m) (eqToHom_refl _ eM)).trans (Category.comp_id g)
  rw [eqToHom_refl, Category.id_comp, hM]
  exact (extendScalars_homEquiv_symm_comp J θ₁ (θ₂ ≫ θ₃) h₁ h₂ h₄ T M g).trans
    (congrArg (fun m ↦ (extendScalarsCompIso J θ₁ (θ₂ ≫ θ₃) h₁ h₂ h₄).hom.app T ≫ m)
      (extendScalars_homEquiv_symm_comp J θ₂ θ₃ h₂ h₃ h₄ ((extendScalars J θ₁ h₁ h₂).obj T) M _))

end ExtendScalarsTranspose

section Step5

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  {Z : RingedTopos.{v'', u'', w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [Z.J.HasSheafCompose (forget RingCat.{w})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (φ : AlgebraicGeometry.RingedToposHom X Y) (ψ : AlgebraicGeometry.RingedToposHom Y Z)

/-- The intermediate presheaf of commutative rings `φ⁻¹(ψ⁻¹O_E)` of the factorisation of the
comm-ring form of the structure map of a composite. -/
abbrev step5CompMid : X.Cᵒᵖ ⥤ CommRingCat.{w} :=
  ((inverseImageCommRingFunctor φ.toToposHom).obj
    ((inverseImageCommRingFunctor ψ.toToposHom).obj Z.O)).obj

omit [Z.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The sheaf condition for the intermediate presheaf of commutative rings of the
factorisation.** `Stacks.SheafOfModules.step5CompMid` is the underlying presheaf of a sheaf of
commutative rings — the iterated inverse image of the structure sheaf of the target — and this is
that sheaf's own condition, read on the underlying presheaf of rings. -/
lemma isSheaf_step5CompMid :
    Presheaf.IsSheaf X.J
      (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf (step5CompMid φ ψ)) :=
  ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
    ((inverseImageCommRingFunctor φ.toToposHom).obj
      ((inverseImageCommRingFunctor ψ.toToposHom).obj Z.O))).property

/-- The first factor of `Stacks.Sheaves.RingedToposModules.fSharpCommRing_comp`: the comparison
`(ψ ∘ φ)⁻¹O_E ≅ φ⁻¹(ψ⁻¹O_E)` of the inverse image along the composite with the iterated inverse
image, on underlying presheaves of commutative rings. -/
abbrev step5CompFactor₁ :
    inverseImageStructureCommRing (ψ.comp φ).toModulesHom ⟶ step5CompMid φ ψ :=
  ((inverseImageCommRingComp ψ.toToposHom φ.toToposHom).inv.app Z.O).hom

/-- The second factor of `Stacks.Sheaves.RingedToposModules.fSharpCommRing_comp`: the inverse
image along `φ` of the comm-ring form of the structure map of `ψ`. -/
abbrev step5CompFactor₂ :
    step5CompMid φ ψ ⟶ inverseImageStructureCommRing φ.toModulesHom :=
  ((inverseImageCommRingFunctor φ.toToposHom).map
    (⟨fSharpCommRing ψ.toModulesHom⟩ :
      (inverseImageCommRingFunctor ψ.toToposHom).obj Z.O ⟶ Y.O)).hom

/-- The third factor of `Stacks.Sheaves.RingedToposModules.fSharpCommRing_comp`: the comm-ring
form of the structure map of `φ`. Extension of scalars along it is
`Stacks.Sheaves.RingedToposModules.extendScalarsFSharp` of `φ`, so the adjunction it carries is
the one step 5 for `φ` is. -/
abbrev step5CompFactor₃ : inverseImageStructureCommRing φ.toModulesHom ⟶ X.O.obj :=
  fSharpCommRing φ.toModulesHom

/-- The tensor product over `(ψ ∘ φ)⁻¹O_E` of the inverse images of the two source modules: the
object that step 5 for the composite is a bijection of morphisms out of.

It is named because the statement of the composition law mentions it four times, and an unnamed
occurrence of it is what makes that statement's elaboration expensive. -/
abbrev step5CompTensor (F G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) :
    SheafOfModules.{w}
      (inverseImageRingSheaf (ψ.comp φ).toModulesHom.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) :=
  inverseImageTensorSheaf (ψ.comp φ).toModulesHom
    ((inverseImageModules (ψ.comp φ).toModulesHom.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj F)
    ((inverseImageModules (ψ.comp φ).toModulesHom.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj G)

/-- **The transport of the source object of step 5 along the factorisation of the structure map
of a composite**: extension of scalars along `(ψ ∘ φ)♯` and along the threefold composite agree
on the tensor product, because the two morphisms are equal. -/
lemma step5CompExtendEq (F G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) :
    (extendScalars X.J (fSharpCommRing (ψ.comp φ).toModulesHom)
        (isSheaf_inverseImageStructureCommRing (ψ.comp φ).toModulesHom)
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).obj (step5CompTensor φ ψ F G) =
      (extendScalars X.J (step5CompFactor₁ φ ψ ≫ step5CompFactor₂ φ ψ ≫ step5CompFactor₃ φ)
        (isSheaf_inverseImageStructureCommRing (ψ.comp φ).toModulesHom)
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).obj (step5CompTensor φ ψ F G) :=
  congrArg
    (fun σ : inverseImageStructureCommRing (ψ.comp φ).toModulesHom ⟶ X.O.obj ↦
      (extendScalars X.J σ (isSheaf_inverseImageStructureCommRing (ψ.comp φ).toModulesHom)
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).obj (step5CompTensor φ ψ F G))
    (fSharpCommRing_comp ψ φ)

omit [Z.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The transport of the sheaf of values of step 5 along the factorisation of the structure map
of a composite**: the restriction of scalars of `N` along `(ψ ∘ φ)♯` is the three restrictions of
scalars along the three factors, taken in turn. -/
lemma step5CompValuesEq (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (SheafOfModules.restrictScalars (ψ.comp φ).toModulesHom.fSharpInverseImage).obj N =
      (SheafOfModules.restrictScalars (commRingSheafMap X.J (step5CompFactor₁ φ ψ)
          (isSheaf_inverseImageStructureCommRing (ψ.comp φ).toModulesHom)
          (isSheaf_step5CompMid φ ψ))).obj
        ((SheafOfModules.restrictScalars (commRingSheafMap X.J (step5CompFactor₂ φ ψ)
            (isSheaf_step5CompMid φ ψ)
            (isSheaf_inverseImageStructureCommRing φ.toModulesHom))).obj
          ((SheafOfModules.restrictScalars (commRingSheafMap X.J (step5CompFactor₃ φ)
              (isSheaf_inverseImageStructureCommRing φ.toModulesHom)
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)).obj N)) :=
  restrictScalars_commRingSheafMap_eq_comp₃ X.J (fSharpCommRing (ψ.comp φ).toModulesHom)
    (step5CompFactor₁ φ ψ) (step5CompFactor₂ φ ψ) (step5CompFactor₃ φ) (fSharpCommRing_comp ψ φ)
    (isSheaf_inverseImageStructureCommRing (ψ.comp φ).toModulesHom) (isSheaf_step5CompMid φ ψ)
    (isSheaf_inverseImageStructureCommRing φ.toModulesHom)
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property N

/-- **The composition law for step 5 of the chain of Tag 03EL.** Let
`φ : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and `ψ : (Sh(D), O_D) ⟶ (Sh(E), O_E)` be morphisms of ringed
topoi, let `F` and `G` be sheaves of `O_E`-modules and `N` a sheaf of `O_C`-modules. A morphism
`g : (ψ ∘ φ)⁻¹F ⊗ (ψ ∘ φ)⁻¹G ⟶ N|_{(ψ ∘ φ)⁻¹O_E}` is carried by step 5 for the composite to the
morphism obtained by transposing back three times — across extension of scalars along the
comparison of the inverse image along the composite with the iterated inverse image, then along
the inverse image of `ψ♯`, then along `φ♯`, that last transposition being step 5's own adjunction
for `φ` — and composing with the two comparisons of extension of scalars along a composite with
the composite of the extensions of scalars.

The two `CategoryTheory.eqToHom` factors are the transports
`Stacks.SheafOfModules.step5CompExtendEq` and `Stacks.SheafOfModules.step5CompValuesEq` along
`Stacks.Sheaves.RingedToposModules.fSharpCommRing_comp`; the implementation notes record why they
are written out rather than left implicit.

It is `Stacks.Sheaves.RingedToposModules.extendScalarsCompIso` twice, read through
`CategoryTheory.Adjunction.leftAdjointUniq_hom_app_comp_homEquiv_symm''`. -/
theorem pullbackTensorStep5_comp
    (F G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (g : step5CompTensor φ ψ F G ⟶
      (SheafOfModules.restrictScalars (ψ.comp φ).toModulesHom.fSharpInverseImage).obj N) :
    pullbackTensorStep5 (ψ.comp φ).toModulesHom F G N g =
      eqToHom (step5CompExtendEq φ ψ F G) ≫
      (extendScalarsCompIso X.J (step5CompFactor₁ φ ψ)
          (step5CompFactor₂ φ ψ ≫ step5CompFactor₃ φ)
          (isSheaf_inverseImageStructureCommRing (ψ.comp φ).toModulesHom)
          (isSheaf_step5CompMid φ ψ) (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).hom.app
        (step5CompTensor φ ψ F G) ≫
      (extendScalarsCompIso X.J (step5CompFactor₂ φ ψ) (step5CompFactor₃ φ)
          (isSheaf_step5CompMid φ ψ)
          (isSheaf_inverseImageStructureCommRing φ.toModulesHom)
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).hom.app
        ((extendScalars X.J (step5CompFactor₁ φ ψ)
          (isSheaf_inverseImageStructureCommRing (ψ.comp φ).toModulesHom)
          (isSheaf_step5CompMid φ ψ)).obj (step5CompTensor φ ψ F G)) ≫
      ((extendRestrictScalarsAdjunction X.J (step5CompFactor₃ φ)
            (isSheaf_inverseImageStructureCommRing φ.toModulesHom)
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).homEquiv
          ((extendScalars X.J (step5CompFactor₂ φ ψ) (isSheaf_step5CompMid φ ψ)
              (isSheaf_inverseImageStructureCommRing φ.toModulesHom)).obj
            ((extendScalars X.J (step5CompFactor₁ φ ψ)
              (isSheaf_inverseImageStructureCommRing (ψ.comp φ).toModulesHom)
              (isSheaf_step5CompMid φ ψ)).obj (step5CompTensor φ ψ F G))) N).symm
        (((extendRestrictScalarsAdjunction X.J (step5CompFactor₂ φ ψ)
              (isSheaf_step5CompMid φ ψ)
              (isSheaf_inverseImageStructureCommRing φ.toModulesHom)).homEquiv
            ((extendScalars X.J (step5CompFactor₁ φ ψ)
              (isSheaf_inverseImageStructureCommRing (ψ.comp φ).toModulesHom)
              (isSheaf_step5CompMid φ ψ)).obj (step5CompTensor φ ψ F G))
            ((SheafOfModules.restrictScalars (commRingSheafMap X.J (step5CompFactor₃ φ)
              (isSheaf_inverseImageStructureCommRing φ.toModulesHom)
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)).obj N)).symm
          (((extendRestrictScalarsAdjunction X.J (step5CompFactor₁ φ ψ)
                (isSheaf_inverseImageStructureCommRing (ψ.comp φ).toModulesHom)
                (isSheaf_step5CompMid φ ψ)).homEquiv (step5CompTensor φ ψ F G)
              ((SheafOfModules.restrictScalars (commRingSheafMap X.J (step5CompFactor₂ φ ψ)
                  (isSheaf_step5CompMid φ ψ)
                  (isSheaf_inverseImageStructureCommRing φ.toModulesHom))).obj
                ((SheafOfModules.restrictScalars (commRingSheafMap X.J (step5CompFactor₃ φ)
                  (isSheaf_inverseImageStructureCommRing φ.toModulesHom)
                  (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)).obj N))).symm
            (g ≫ eqToHom (step5CompValuesEq φ ψ N)))) :=
  extendScalars_homEquiv_symm_comp₃ X.J (fSharpCommRing (ψ.comp φ).toModulesHom)
    (step5CompFactor₁ φ ψ) (step5CompFactor₂ φ ψ) (step5CompFactor₃ φ) (fSharpCommRing_comp ψ φ)
    (isSheaf_inverseImageStructureCommRing (ψ.comp φ).toModulesHom) (isSheaf_step5CompMid φ ψ)
    (isSheaf_inverseImageStructureCommRing φ.toModulesHom)
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
    (step5CompTensor φ ψ F G) N (step5CompExtendEq φ ψ F G) (step5CompValuesEq φ ψ N) g

end Step5

end Stacks.SheafOfModules

end
