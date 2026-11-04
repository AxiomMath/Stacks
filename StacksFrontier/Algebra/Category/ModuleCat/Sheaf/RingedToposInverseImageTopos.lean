module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesOfIsoStructureMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposInverseImageExact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The ringed topos `(Sh(C), f⁻¹O_D)` of a morphism of ringed topoi

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi. The inverse image
`f⁻¹O_D` is a sheaf of commutative rings on `C`, so `(Sh(C), f⁻¹O_D)` is a ringed topos, and `f`
factors as

`(Sh(C), O_C) ⟶ (Sh(C), f⁻¹O_D) ⟶ (Sh(D), O_D)`,

the second morphism being `f` with the identity of `f⁻¹O_D` as the inverse-image form of its
structure map. Pullback of sheaves of modules along the second morphism is the inverse image of
sheaves of modules, extended along an identity, so it is exact. This is the factorization through
which the proof of Tag 0FSI (2) reads `f^*𝒫 = f⁻¹𝒫 ⊗_{f⁻¹𝒜} 𝒜'`.

## Main definitions

* `Stacks.Sheaves.RingedToposModules.RingedToposHom.inverseImageRingedTopos`: the ringed topos
  `(Sh(C), f⁻¹O_D)`, whose structure sheaf is `inverseImageStructureCommRing f` on the nose.
* `Stacks.Sheaves.RingedToposModules.RingedToposHom.inverseImageRingedToposHom`: the morphism of
  ringed topoi `(Sh(C), f⁻¹O_D) ⟶ (Sh(D), O_D)` with underlying morphism of topoi `f`.
* `Stacks.Sheaves.RingedToposModules.RingedToposHom.coefficientMap`: the inverse-image form
  `f⁻¹O_D ⟶ O_C` of the structure map, as a morphism of sheaves of commutative rings.

## Main results

* `RingedToposHom.acyclic_map_pullbackModules_inverseImageRingedToposHom`: pullback of sheaves
  of modules along `(Sh(C), f⁻¹O_D) ⟶ (Sh(D), O_D)` carries acyclic complexes
  to acyclic complexes.

## References

* [Stacks Project, Tag 0FSI](https://stacks.math.columbia.edu/tag/0FSI)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe v u w v' u' w'

namespace Stacks.Sheaves.RingedToposModules.RingedToposHom

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : RingedToposHom X Y)

/-- The inverse image `f⁻¹O_D` of the structure sheaf of the target, as a sheaf of commutative
rings on the source site. Its underlying presheaf is `inverseImageStructureCommRing f`. -/
def inverseImageStructureSheaf : Sheaf X.J CommRingCat.{w} :=
  ⟨inverseImageStructureCommRing f,
    Presheaf.isSheaf_of_isSheaf_comp X.J _ (forget₂ CommRingCat.{w} RingCat.{w})
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property⟩

/-- **The ringed topos `(Sh(C), f⁻¹O_D)`**: the site of the source with the inverse image of the
structure sheaf of the target. -/
def inverseImageRingedTopos : RingedTopos.{v, u, w} :=
  ⟨X.C, X.J, inverseImageStructureSheaf f⟩

instance : (inverseImageRingedTopos f).J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) :=
  inferInstanceAs (X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}))

instance : (inverseImageRingedTopos f).J.HasSheafCompose (forget RingCat.{w}) :=
  inferInstanceAs (X.J.HasSheafCompose (forget RingCat.{w}))

instance : (inverseImageRingedTopos f).J.HasSheafCompose (forget AddCommGrpCat.{w}) :=
  inferInstanceAs (X.J.HasSheafCompose (forget AddCommGrpCat.{w}))

instance [HasWeakSheafify X.J AddCommGrpCat.{w}] :
    HasWeakSheafify (inverseImageRingedTopos f).J AddCommGrpCat.{w} :=
  inferInstanceAs (HasWeakSheafify X.J AddCommGrpCat.{w})

instance [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] :
    (inverseImageRingedTopos f).J.WEqualsLocallyBijective AddCommGrpCat.{w} :=
  inferInstanceAs (X.J.WEqualsLocallyBijective AddCommGrpCat.{w})

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- The structure sheaf of rings of `(Sh(C), f⁻¹O_D)` is the inverse-image sheaf of rings
`f⁻¹O_D`, on the nose. -/
theorem ringSheaf_inverseImageRingedTopos :
    Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingedTopos f).O =
      inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) :=
  rfl

/-- **The morphism of ringed topoi `(Sh(C), f⁻¹O_D) ⟶ (Sh(D), O_D)`**: the morphism of topoi
`f`, with the unit `O_D ⟶ f_*f⁻¹O_D` as its structure map and the identity of `f⁻¹O_D` as the
inverse-image form of it. -/
def inverseImageRingedToposHom : RingedToposHom (inverseImageRingedTopos f) Y where
  toToposHom := f.toToposHom
  fSharp := ringUnit f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
  fSharpInverseImage := 𝟙 _
  fSharp_adjunct := by
    change _ = f.toToposHom.adj.homEquiv _ _
      ((sheafCompose X.J (forget RingCat.{w})).map
        (𝟙 (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))
    rw [CategoryTheory.Functor.map_id]
    exact (homEquiv_id_eq_ringUnit f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).symm

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- The inverse-image form of the structure map of `(Sh(C), f⁻¹O_D) ⟶ (Sh(D), O_D)` is the
identity. -/
@[simp]
theorem inverseImageRingedToposHom_fSharpInverseImage :
    (inverseImageRingedToposHom f).fSharpInverseImage = 𝟙 _ :=
  rfl

instance isIso_inverseImageRingedToposHom_fSharpInverseImage :
    IsIso (inverseImageRingedToposHom f).fSharpInverseImage :=
  IsIso.id (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

/-- **The inverse-image form `f⁻¹O_D ⟶ O_C` of the structure map**, as a morphism from the
structure sheaf of `(Sh(C), f⁻¹O_D)` to that of `(Sh(C), O_C)`, of sheaves of commutative
rings. -/
def coefficientMap : (inverseImageRingedTopos f).O ⟶ X.O :=
  ⟨fSharpCommRing f⟩

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- On underlying sheaves of rings, the coefficient map is the inverse-image form of the
structure map of `f`. -/
theorem coefficientMap_ringSheaf :
    (sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map (coefficientMap f) =
      f.fSharpInverseImage :=
  rfl

variable [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Pullback of sheaves of modules along `(Sh(C), f⁻¹O_D) ⟶ (Sh(D), O_D)` preserves finite
limits: it is the inverse image of sheaves of modules, which is left exact, followed by extension
of scalars along an isomorphism, which is an equivalence. -/
instance preservesFiniteLimits_pullbackModules_inverseImageRingedToposHom :
    PreservesFiniteLimits (pullbackModules (inverseImageRingedToposHom f)) := by
  have e := (inverseImageRingedToposHom f).extendScalarsFSharpIsoRestrictScalarsOfIsIso
  have : PreservesFiniteLimits (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
      (asIso (inverseImageRingedToposHom f).fSharpInverseImage)).functor := inferInstance
  have : PreservesFiniteLimits (SheafOfModules.restrictScalars
      (asIso (inverseImageRingedToposHom f).fSharpInverseImage).inv) := this
  have : PreservesFiniteLimits (extendScalarsFSharp (inverseImageRingedToposHom f)) :=
    preservesFiniteLimits_of_natIso e.symm
  exact comp_preservesFiniteLimits _ _

/-- Pullback of sheaves of modules along `(Sh(C), f⁻¹O_D) ⟶ (Sh(D), O_D)` preserves finite
colimits, being a left adjoint. -/
@[sga "4 IV 13.6" "special case"]
instance preservesFiniteColimits_pullbackModules_inverseImageRingedToposHom :
    PreservesFiniteColimits (pullbackModules (inverseImageRingedToposHom f)) := by
  have : PreservesColimitsOfSize.{0, 0} (pullbackModules (inverseImageRingedToposHom f)) :=
    (pullbackAdjPushforwardModules (inverseImageRingedToposHom f)).leftAdjoint_preservesColimits
  exact PreservesColimitsOfSize.preservesFiniteColimits _

/-- Pullback of sheaves of modules along `(Sh(C), f⁻¹O_D) ⟶ (Sh(D), O_D)` is additive, being a
left adjoint. -/
instance additive_pullbackModules_inverseImageRingedToposHom :
    (pullbackModules (inverseImageRingedToposHom f)).Additive :=
  (pullbackAdjPushforwardModules (inverseImageRingedToposHom f)).left_adjoint_additive

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- **Pullback along `(Sh(C), f⁻¹O_D) ⟶ (Sh(D), O_D)` is exact on complexes**: it carries an
acyclic complex of sheaves of `O_D`-modules to an acyclic complex. -/
theorem acyclic_map_pullbackModules_inverseImageRingedToposHom
    (K : CochainComplex (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : K.Acyclic) :
    (((pullbackModules (inverseImageRingedToposHom f)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).Acyclic :=
  fun n => (HomologicalComplex.exactAt_iff _ _).2
    (((HomologicalComplex.exactAt_iff _ _).1 (hK n)).map
      (pullbackModules (inverseImageRingedToposHom f)))

end Stacks.Sheaves.RingedToposModules.RingedToposHom

end
