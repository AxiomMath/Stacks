module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FlatDeformation.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Thickenings.SquareZeroExtensionFunctor
public import StacksFrontier.Deformation.ToposThickening.SolutionAutomorphisms
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Sheaf

/-!
# Realizing a solution of the deformation problem by a scheme
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite
open Stacks.Sheaves.RingedSpaceDifferentials (sheafAdjunction inverseImageStructureMap
  structureSheafMap)
open Deformation.ToposThickening.RingedToposExtensionProblem

universe u

namespace Stacks.Thickenings.FlatDeformation

variable {X S S' : Scheme.{u}} {t : S ⟶ S'} {f : X ⟶ S} [IsClosedImmersion t]
  (hst : t.ker ^ 2 = ⊥)
  {c : ideal t f hst ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
        (structureHom f).fSharpInverseImage)).obj (conormalModule t f)}

/-- The morphism of sheafed spaces with identity underlying map attached to a morphism of sheaves
of rings on `X`. -/
def thickenedHom {A B : TopCat.Sheaf CommRingCat.{u} X} (φ : B ⟶ A) :
    thickenedSpace X A ⟶ thickenedSpace X B :=
  InducedCategory.homMk { base := 𝟙 (X : TopCat), c := φ.hom }

/-- The morphism of sheafed spaces from the space of `X` with structure sheaf `A` to `S'`, with
underlying map `t ∘ f` and comorphism `β : 𝒪_{S'} ⟶ (t ∘ f)_* A`. -/
def thickenedToBase {A : TopCat.Sheaf CommRingCat.{u} X}
    (β : S'.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} (f.base ≫ t.base)).obj A) :
    thickenedSpace X A ⟶ S'.toSheafedSpace :=
  InducedCategory.homMk { base := f.base ≫ t.base, c := β.hom }

/-- A morphism of sheafed spaces with identity underlying map between two ringed structures on the
space of `X`, read as a morphism of sheaves of rings. -/
def sheafOfThickened {A B : TopCat.Sheaf CommRingCat.{u} X}
    (Φ : thickenedSpace X A ⟶ thickenedSpace X B) (h : Φ.hom.base = 𝟙 (X : TopCat)) : B ⟶ A :=
  ⟨Φ.hom.c ≫ eqToHom (congrArg (fun g => (TopCat.Presheaf.pushforward CommRingCat.{u} g).obj
    A.presheaf) h)⟩

/-- `thickenedHom` and `sheafOfThickened` are inverse on morphisms with identity underlying
map. -/
theorem thickenedHom_sheafOfThickened {A B : TopCat.Sheaf CommRingCat.{u} X}
    (Φ : thickenedSpace X A ⟶ thickenedSpace X B) (h : Φ.hom.base = 𝟙 (X : TopCat)) :
    thickenedHom (sheafOfThickened Φ h) = Φ := by
  obtain ⟨⟨b, c⟩⟩ := Φ
  change b = 𝟙 (X : TopCat) at h
  subst h
  rfl

/-- `thickenedHom` is injective. -/
theorem thickenedHom_injective {A B : TopCat.Sheaf CommRingCat.{u} X} {φ ψ : B ⟶ A}
    (h : thickenedHom φ = thickenedHom ψ) : φ = ψ :=
  Sheaf.hom_ext (NatTrans.ext (funext fun U => by
    have := PresheafedSpace.congr_app (congrArg InducedCategory.Hom.hom h) U
    change φ.hom.app U = ψ.hom.app U ≫ _ at this
    refine this.trans ?_
    have e : (eqToHom (show op U.unop = op U.unop from rfl) : op U.unop ⟶ op U.unop) = 𝟙 _ :=
      eqToHom_refl _ _
    refine (congrArg (ψ.hom.app U ≫ ·) ((congrArg A.presheaf.map e).trans
      (A.presheaf.map_id _))).trans (Category.comp_id _)))

omit [IsClosedImmersion t] in
/-- `thickenedHom ρ` followed by `thickenedToBase β` is `thickenedToBase` of `β` followed by the
pushforward of `ρ`. -/
theorem thickenedHom_comp_thickenedToBase {A B : TopCat.Sheaf CommRingCat.{u} X} (ρ : B ⟶ A)
    (β : S'.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} (f.base ≫ t.base)).obj B) :
    thickenedHom ρ ≫ thickenedToBase β =
      thickenedToBase (β ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} (f.base ≫ t.base)).map ρ) :=
  rfl

omit [IsClosedImmersion t] in
/-- `thickenedToBase` is injective. -/
theorem thickenedToBase_injective {A : TopCat.Sheaf CommRingCat.{u} X}
    {β β' : S'.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} (f.base ≫ t.base)).obj A}
    (h : thickenedToBase (t := t) (f := f) β = thickenedToBase β') : β = β' :=
  Sheaf.hom_ext (NatTrans.ext (funext fun U => by
    have := PresheafedSpace.congr_app (congrArg InducedCategory.Hom.hom h) U
    change β.hom.app U = β'.hom.app U ≫ _ at this
    refine this.trans ?_
    have e : (eqToHom (show op ((Opens.map (f.base ≫ t.base)).obj U.unop) =
        op ((Opens.map (f.base ≫ t.base)).obj U.unop) from rfl) :
          op ((Opens.map (f.base ≫ t.base)).obj U.unop) ⟶ _) = 𝟙 _ :=
      eqToHom_refl _ _
    exact (congrArg (β'.hom.app U ≫ ·) ((congrArg A.presheaf.map e).trans
      (A.presheaf.map_id _))).trans (Category.comp_id _)))

variable {hst} (P : (problem t f hst c).CompatibleFirstOrderThickening)

/-- The map from the thickened base ring of a solution, without the inverse image along the
identity. -/
abbrev baseMap₀ : thickenedBaseRing t f ⟶ P.extension :=
  (idIso f (thickenedBaseRing t f)).inv ≫ P.baseMap

/-- `baseMap₀ P` followed by the reduction is the structure map `(t ∘ f)⁻¹𝒪_{S'} ⟶ 𝒪_X`. -/
theorem baseMap₀_comp_reduction :
    baseMap₀ P ≫ P.reduction = inverseImageStructureMap
      (f.toLRSHom.toShHom ≫ t.toLRSHom.toShHom) :=
  (Category.assoc _ _ _).trans ((congrArg ((idIso f (thickenedBaseRing t f)).inv ≫ ·)
    (P.baseMap_reduction.trans (rebuiltReduction_comp_fSharpInverseImage t f))).trans
    (Iso.inv_hom_id_assoc _ _))

/-- The comorphism `𝒪_{S'} ⟶ (t ∘ f)_* 𝒪'` of a solution. -/
abbrev baseComorphism : S'.sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat.{u} (f.base ≫ t.base)).obj P.extension :=
  (sheafAdjunction (f.toLRSHom.toShHom ≫ t.toLRSHom.toShHom)).homEquiv _ _ (baseMap₀ P)

/-- `baseComorphism P` followed by the pushforward of the reduction is the comorphism
`𝒪_{S'} ⟶ (t ∘ f)_* 𝒪_X`. -/
theorem baseComorphism_comp_reduction :
    baseComorphism P ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} (f.base ≫ t.base)).map
      P.reduction = structureSheafMap (f.toLRSHom.toShHom ≫ t.toLRSHom.toShHom) :=
  (Adjunction.homEquiv_naturality_right _ _ _).symm.trans ((congrArg _
    (baseMap₀_comp_reduction P)).trans
    (Stacks.Sheaves.RingedSpaceDifferentials.homEquiv_inverseImageStructureMap _))

/-- **The square-zero extension of `𝒪_X` over `S'` underlying a solution**, in the sense of
[Stacks Project, Tag 05YV]. -/
def toSquareZeroExtension : Stacks.Thickenings.SquareZeroExtension (f ≫ t) where
  A := P.extension
  π := P.reduction
  locallySurjective_π := P.locallySurjective
  inclusion := thickenedHom P.reduction
  inclusion_base := rfl
  inclusion_sheaf := HEq.rfl
  toBase := thickenedToBase (baseComorphism P)
  over_base := InducedCategory.hom_ext (PresheafedSpace.hext _ _ rfl
    (heq_of_eq (congrArg (fun φ => φ.hom) (baseComorphism_comp_reduction P))))
  I := pullbackConormalModule f t
  quasicoherent := AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent
    f.toLRSHom.toShHom (Stacks.Conormal.conormalSheaf t)
  ι U := (P.kernelInclusion.val.app U).hom.toAddMonoidHom
  naturality g x := ConcreteCategory.congr_hom (P.kernelInclusion.val.naturality g) x
  mem_kernel U x := P.kernelZero U x
  exact_kernel U a ha := P.kernelUniversal U a ha
  smul_lift _ a x := (P.mul_incl a x).symm
  square_zero _ x y := P.incl_mul_incl x y

/-- `thickenedHom` reverses composition. -/
theorem thickenedHom_comp {A B C : TopCat.Sheaf CommRingCat.{u} X} (φ : B ⟶ A) (ψ : C ⟶ B) :
    thickenedHom φ ≫ thickenedHom ψ = thickenedHom (ψ ≫ φ) :=
  rfl

/-- `thickenedHom` sends the identity to the identity. -/
theorem thickenedHom_id (A : TopCat.Sheaf CommRingCat.{u} X) :
    thickenedHom (𝟙 A) = 𝟙 (thickenedSpace X A) :=
  rfl

/-- **An isomorphism of solutions is a morphism of the underlying square-zero extensions.** -/
def squareZeroHom {P Q : (problem t f hst c).CompatibleFirstOrderThickening}
    (e : CompatibleFirstOrderThickening.Iso.{u, u, u, u, u, u} (S := problem t f hst c) P Q) :
    (toSquareZeroExtension P).Hom (toSquareZeroExtension Q) where
  base := 𝟙 X
  sheafHom := thickenedHom e.hom.inv
  inclusion_comm :=
    (thickenedHom_comp _ _).trans ((congrArg thickenedHom
      ((congrArg (e.hom.inv ≫ ·) e.reduction_comm.symm).trans
        (Iso.inv_hom_id_assoc _ _))).trans (Category.id_comp _).symm)
  toBase_comm := by
    have h : baseMap₀ Q ≫ e.hom.inv = baseMap₀ P :=
      (Category.assoc _ _ _).trans (congrArg ((idIso f (thickenedBaseRing t f)).inv ≫ ·)
        ((congrArg (· ≫ e.hom.inv) e.baseMap_comm.symm).trans ((Category.assoc _ _ _).trans
          ((congrArg (P.baseMap ≫ ·) e.hom.hom_inv_id).trans (Category.comp_id _)))))
    have h' : baseComorphism Q ≫ (TopCat.Sheaf.pushforward CommRingCat.{u}
        (f.base ≫ t.base)).map e.hom.inv = baseComorphism P :=
      (Adjunction.homEquiv_naturality_right _ _ _).symm.trans (congrArg _ h)
    exact InducedCategory.hom_ext (PresheafedSpace.hext _ _ rfl
      (heq_of_eq (congrArg (fun φ => φ.hom) h')))

/-- `squareZeroHom` sends a composite of isomorphisms of solutions to the composite of
morphisms of square-zero extensions. -/
theorem squareZeroHom_trans {P Q R : (problem t f hst c).CompatibleFirstOrderThickening}
    (e : CompatibleFirstOrderThickening.Iso.{u, u, u, u, u, u} (S := problem t f hst c) P Q)
    (e' : CompatibleFirstOrderThickening.Iso.{u, u, u, u, u, u} (S := problem t f hst c) Q R) :
    (squareZeroHom e).comp (squareZeroHom e') = squareZeroHom (e.trans e') :=
  SquareZeroExtension.Hom.ext (Category.id_comp _) rfl

/-- `squareZeroHom` sends the identity isomorphism to the identity. -/
theorem squareZeroHom_refl (P : (problem t f hst c).CompatibleFirstOrderThickening) :
    squareZeroHom (CompatibleFirstOrderThickening.Iso.refl.{u, u, u, u, u, u} P) =
      SquareZeroExtension.Hom.id (toSquareZeroExtension P) :=
  SquareZeroExtension.Hom.ext rfl rfl

/-! ### The transport of a thickening, as an isomorphism of sheafed spaces -/

section Ambient

variable {X' : Scheme.{u}} (i : X ⟶ X') [IsIso i.base] [IsClosedImmersion i]

/-- The sheafed space `X'` is isomorphic to the space of `X` with the transported structure
sheaf. -/
def ambientIso : X'.toSheafedSpace ≅ thickenedSpace X (transported i) :=
  SheafedSpace.isoMk (PresheafedSpace.isoOfComponents (asIso i.base).symm (Iso.refl _))

omit [IsClosedImmersion i] in
/-- `i` followed by `ambientIso i` is `thickenedHom` of the transported reduction. -/
theorem ambientIso_inclusion :
    i.toLRSHom.toShHom ≫ (ambientIso i).hom = thickenedHom (transportedReduction i) := by
  apply SheafedSpace.ext _ _ (asIso i.base).hom_inv_id
  apply NatTrans.ext
  funext U
  change (𝟙 _ ≫ i.app _) ≫ X.presheaf.map _ = i.app _ ≫ X.presheaf.map _
  simp only [Category.id_comp]
  congr 2
  exact Subsingleton.elim _ _

omit [IsClosedImmersion t] [IsClosedImmersion i] in
/-- The inverse of `ambientIso i` followed by `f'` is `thickenedToBase` of the transported
comorphism of `f'`. -/
theorem ambientIso_toBase {f' : X' ⟶ S'} (comm : i ≫ f' = f ≫ t) :
    (ambientIso i).inv ≫ f'.toLRSHom.toShHom =
      thickenedToBase (transportedBase i comm) := by
  apply SheafedSpace.ext _ _ (show i.base ≫ f'.base = f.base ≫ t.base by
    rw [← Scheme.Hom.comp_base, comm]; rfl)
  apply NatTrans.ext
  funext V
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  change _ = ((transportedBase i comm).hom.app (op V.unop)) a
  rw [transportedBase_app]
  change (X'.presheaf.map _) ((X'.presheaf.map _) ((f'.app _).hom a)) = _
  exact (scheme_map_comp_apply _ _ _).trans
    (congrArg (fun g => (X'.presheaf.map g).hom _) (Subsingleton.elim _ _))

end Ambient

/-! ### A flat deformation realizes its own solution -/

section Deformation

variable (D : FlatDeformation t f) [IsIso D.i.base] (hc : c = idealMap hst D)

/-- The comorphism of the solution of a flat deformation is the transported comorphism of
`f'`. -/
theorem baseComorphism_toSolution :
    baseComorphism (toSolution hst D c hc) = transportedBase D.i D.isPullback.w := by
  have hb : (baseMap₀ (toSolution hst D c hc)) = baseRingMap D :=
    Iso.inv_hom_id_assoc _ _
  change (sheafAdjunction _).homEquiv _ _ _ = _
  rw [hb]
  exact Equiv.apply_symm_apply _ _

/-- The inverse of `ambientIso D.i` followed by `D.f'` is the morphism to `S'` of the square-zero
extension of the solution of `D`. -/
theorem toBase_eq :
    (ambientIso D.i).inv ≫ D.f'.toLRSHom.toShHom =
      (toSquareZeroExtension (toSolution hst D c hc)).toBase := by
  refine (ambientIso_toBase D.i D.isPullback.w).trans ?_
  change _ = thickenedToBase (baseComorphism (toSolution hst D c hc))
  rw [baseComorphism_toSolution]
  rfl

/-- **A flat deformation realizes the square-zero extension of its solution.** -/
def realization : Realization (toSquareZeroExtension (toSolution hst D c hc)) where
  ambient := D.X'
  sheafedIso := ambientIso D.i
  immersion := D.i
  toBase := D.f'
  immersion_isFirstOrder := ⟨inferInstance, D.ker_sq hst⟩
  over_base := D.isPullback.w
  inclusion_eq := ambientIso_inclusion D.i
  toBase_eq := toBase_eq D hc

omit [IsIso D.i.base] in
/-- **Isomorphic solutions come from isomorphic flat deformations.** -/
def isoOfSolutionIso (D₁ D₂ : FlatDeformation t f) [IsIso D₁.i.base] [IsIso D₂.i.base]
    (hc₁ : c = idealMap hst D₁) (hc₂ : c = idealMap hst D₂)
    (e : CompatibleFirstOrderThickening.Iso.{u, u, u, u, u, u} (S := problem t f hst c)
      (toSolution hst D₁ c hc₁) (toSolution hst D₂ c hc₂)) :
    FlatDeformation.Iso D₁ D₂ where
  e :=
    { hom := (realization D₁ hc₁).map (realization D₂ hc₂) (squareZeroHom e)
      inv := (realization D₂ hc₂).map (realization D₁ hc₁) (squareZeroHom e.symm)
      hom_inv_id :=
        ((Realization.map_comp _ _ (realization D₁ hc₁) _ _).symm.trans
          (congrArg _ ((squareZeroHom_trans e e.symm).trans ((congrArg squareZeroHom
            (CompatibleFirstOrderThickening.Iso.ext (e := e.trans e.symm)
              (f := CompatibleFirstOrderThickening.Iso.refl (toSolution hst D₁ c hc₁))
              (Iso.self_symm_id e.hom))).trans
              (squareZeroHom_refl (toSolution hst D₁ c hc₁)))))).trans (Realization.map_id _)
      inv_hom_id :=
        ((Realization.map_comp _ _ (realization D₂ hc₂) _ _).symm.trans
          (congrArg _ ((squareZeroHom_trans e.symm e).trans ((congrArg squareZeroHom
            (CompatibleFirstOrderThickening.Iso.ext (e := e.symm.trans e)
              (f := CompatibleFirstOrderThickening.Iso.refl (toSolution hst D₂ c hc₂))
              (Iso.symm_self_id e.hom))).trans
              (squareZeroHom_refl (toSolution hst D₂ c hc₂)))))).trans (Realization.map_id _) }
  comm_i := ((realization D₁ hc₁).map_immersion (realization D₂ hc₂) (squareZeroHom e)).trans
    (Category.id_comp _)
  comm_f' := (realization D₁ hc₁).map_toBase (realization D₂ hc₂) (squareZeroHom e)

end Deformation

end Stacks.Thickenings.FlatDeformation
