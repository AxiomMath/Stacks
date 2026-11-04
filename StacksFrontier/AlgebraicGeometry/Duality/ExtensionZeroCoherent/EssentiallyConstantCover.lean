module

public import StacksFrontier.Algebra.Homology.DerivedCategory.EssentiallyConstant
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.EventualExtVanishing
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemTriangleExtensionCoherent
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.DerivedDirectImage
public import StacksFrontier.CategoryTheory.EssentiallyConstant.Transport
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.UnboundedTriangle

/-!
# Essential constancy of an inverse system in `D^b_{Coh}` is local

Let `Y` be a locally Noetherian scheme covered by two opens `A` and `B`, and let `(K_n)` be an
inverse system in `D^b_{Coh}(𝒪_Y)`. If the restricted systems `(K_n|_A)`, `(K_n|_B)` and
`(K_n|_{A ∩ B})` are essentially constant pro-objects, then so is `(K_n)`.

This is the step of the proof of [Stacks, Tag 0G4T] which shows that the restriction of the
system to the open `U` is essentially constant: there it is deduced from the distinguished
triangles of Mayer--Vietoris type and Stacks 0G3A. The argument here is the same. The
Mayer--Vietoris triangle of Stacks 08BU,

`j_{A∩B,!}(K|_{A∩B}) ⟶ j_{A,!}(K|_A) ⊕ j_{B,!}(K|_B) ⟶ K ⟶ j_{A∩B,!}(K|_{A∩B})[1]`,

is natural in `K`, so applied to the terms of the system it gives an inverse system of
distinguished triangles. Its two outer vertex systems are essentially constant, being obtained
from the essentially constant restricted systems by exact functors (and, for the middle term of
the triangle, by a biproduct, handled by Stacks 0G3A for the split triangles). Stacks 0G3A then
gives essential constancy of the remaining vertex system `(K_n)` in `D(𝒪_Y)`, and its value lies
in `D^b_{Coh}(𝒪_Y)` because it is a retract of a term of the system.

## Main results

* `CategoryTheory.Pretriangulated.isEssentiallyConstantPro_of_natTriangle`: for a natural family
  of distinguished triangles `P E ⟶ Q E ⟶ E ⟶ (P E)[1]`, an inverse system `G` is essentially
  constant as soon as `G ⋙ P` and `G ⋙ Q` are.
* `AlgebraicGeometry.isEssentiallyConstantPro_of_cover`: the locality statement above.

## References

* [Stacks Project, Tag 0G4T](https://stacks.math.columbia.edu/tag/0G4T)
* [Stacks Project, Tag 0G3A](https://stacks.math.columbia.edu/tag/0G3A)
* [Stacks Project, Tag 08BU](https://stacks.math.columbia.edu/tag/08BU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace CategoryTheory.EssentiallyConstantPro

/-- Being an essentially constant pro-object is invariant under isomorphism of diagrams. -/
public lemma IsEssentiallyConstantPro.of_iso {J C : Type*} [Category J] [Category C]
    {M N : J ⥤ C} (e : M ≅ N) (h : IsEssentiallyConstantPro M) : IsEssentiallyConstantPro N := by
  obtain ⟨c, i, s, hs⟩ := h
  exact ⟨_, i, _, hs.postcompose e⟩

/-- Being an essentially constant pro-object is preserved by postcomposition with a functor. -/
public lemma IsEssentiallyConstantPro.comp {J C D : Type*} [Category J] [Category C] [Category D]
    {M : J ⥤ C} (h : IsEssentiallyConstantPro M) (F : C ⥤ D) :
    IsEssentiallyConstantPro (M ⋙ F) := by
  obtain ⟨c, i, s, hs⟩ := h
  exact ⟨_, i, _, hs.map F⟩

end CategoryTheory.EssentiallyConstantPro

namespace CategoryTheory.Pretriangulated

open EssentiallyConstantPro

variable {𝒟 : Type*} [Category 𝒟] [Preadditive 𝒟] [HasZeroObject 𝒟] [HasShift 𝒟 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟]
  {J : Type*} [Category J] [IsCofiltered J]

/-- **Essential constancy along a natural family of distinguished triangles.** Let
`P E ⟶ Q E ⟶ E ⟶ (P E)[1]` be distinguished triangles, natural in `E`. If `G` is an inverse
system for which `G ⋙ P` and `G ⋙ Q` are essentially constant pro-objects, then `G` is one.

This is Stacks 0G3A applied to the rotated triangles `Q G_j ⟶ G_j ⟶ (P G_j)[1] ⟶ (Q G_j)[1]`,
whose outer vertex systems are essentially constant. -/
public theorem isEssentiallyConstantPro_of_natTriangle {P Q : 𝒟 ⥤ 𝒟} (a : P ⟶ Q)
    (b : Q ⟶ 𝟭 𝒟) (δ : 𝟭 𝒟 ⟶ P ⋙ shiftFunctor 𝒟 (1 : ℤ))
    (hT : ∀ E, Triangle.mk (a.app E) (b.app E) (δ.app E) ∈ distTriang 𝒟) (G : J ⥤ 𝒟)
    (hP : IsEssentiallyConstantPro (G ⋙ P)) (hQ : IsEssentiallyConstantPro (G ⋙ Q)) :
    IsEssentiallyConstantPro G := by
  let T : J ⥤ Triangle 𝒟 := G ⋙ Triangle.functorMk a b δ ⋙ rotate 𝒟
  have hT' : ∀ j, T.obj j ∈ distTriang 𝒟 := fun j => rot_of_distTriang _ (hT (G.obj j))
  have h₁ : EssentiallyConstantInd.IsEssentiallyConstantInd (T ⋙ Triangle.π₁).op :=
    (isEssentiallyConstantPro_iff_op (G ⋙ Q)).mp hQ
  have h₃ : EssentiallyConstantInd.IsEssentiallyConstantInd (T ⋙ Triangle.π₃).op :=
    (isEssentiallyConstantPro_iff_op ((G ⋙ P) ⋙ shiftFunctor 𝒟 (1 : ℤ))).mp
      (hP.comp (shiftFunctor 𝒟 (1 : ℤ)))
  exact (isEssentiallyConstantPro_iff_op G).mpr
    (isEssentiallyConstant_op_π₂_and_exists_limit_triangle T hT' h₁ h₃).1

/-- **Essential constancy of a biproduct.** If `G₁` and `G₂` are essentially constant inverse
systems and `G₁ ⟶ H ⟶ G₂` are natural transformations such that every
`G₁ j ⟶ H j ⟶ G₂ j ⟶ (G₁ j)[1]` with zero third map is distinguished — for instance if `H j` is
the biproduct `G₁ j ⊞ G₂ j` — then `H` is essentially constant. This is Stacks 0G3A for these
split triangles. -/
public theorem isEssentiallyConstantPro_of_split {G₁ H G₂ : J ⥤ 𝒟} (i : G₁ ⟶ H) (p : H ⟶ G₂)
    (hT : ∀ j, Triangle.mk (i.app j) (p.app j) (0 : G₂.obj j ⟶ (G₁.obj j)⟦(1 : ℤ)⟧) ∈
      distTriang 𝒟)
    (h₁ : IsEssentiallyConstantPro G₁) (h₂ : IsEssentiallyConstantPro G₂) :
    IsEssentiallyConstantPro H := by
  let T : J ⥤ Triangle 𝒟 :=
    Triangle.functorMk i p (0 : G₂ ⟶ G₁ ⋙ shiftFunctor 𝒟 (1 : ℤ))
  exact (isEssentiallyConstantPro_iff_op H).mpr
    (isEssentiallyConstant_op_π₂_and_exists_limit_triangle T hT
      ((isEssentiallyConstantPro_iff_op G₁).mp h₁)
      ((isEssentiallyConstantPro_iff_op G₂).mp h₂)).1

end CategoryTheory.Pretriangulated

namespace AlgebraicGeometry

open CategoryTheory.EssentiallyConstantPro Stacks.ExtensionByZero

variable {Y : Scheme.{u}}

/-- The restriction of an essentially constant system in `D^b_{Coh}(𝒪_Y)` to an open `W`, followed
by extension by zero back to `Y`, is an essentially constant system of `D(𝒪_Y)`. -/
public lemma isEssentiallyConstantPro_derivedExtensionRestriction [IsLocallyNoetherian Y]
    (W : Y.Opens) (G : ℕᵒᵖ ⥤ BoundedCoherentDerived Y)
    (hW : IsEssentiallyConstantPro (G ⋙ restrictBoundedCoherentLift W.ι)) :
    IsEssentiallyConstantPro
      ((G ⋙ (boundedCoherentDerived Y).ι) ⋙ derivedExtensionRestriction Y.ringCatSheaf W) := by
  have h₁ : IsEssentiallyConstantPro ((G ⋙ (boundedCoherentDerived Y).ι) ⋙
      Stacks.Duality.OpenImmersion.derivedRestrict W.ι) :=
    hW.comp (boundedCoherentDerived W.toScheme).ι
  have h₂ : IsEssentiallyConstantPro ((G ⋙ (boundedCoherentDerived Y).ι) ⋙
      derivedRestriction Y.ringCatSheaf W) :=
    h₁.of_iso (Functor.isoWhiskerLeft _ (Stacks.DerivedQCoh.derivedRestrictionIso W).symm)
  exact h₂.comp (ExtensionByZeroModules.jShriek W Y.ringCatSheaf).mapDerivedCategory

/-- The middle vertex system `(K_n|_A)_! ⊕ (K_n|_B)_!` of the Mayer--Vietoris triangles is
essentially constant as soon as `(K_n|_A)` and `(K_n|_B)` are: Stacks 0G3A for split
triangles. -/
private lemma isEssentiallyConstantPro_derivedCoverMiddle [IsLocallyNoetherian Y]
    (A B : Y.Opens) (G : ℕᵒᵖ ⥤ BoundedCoherentDerived Y)
    (hA : IsEssentiallyConstantPro (G ⋙ restrictBoundedCoherentLift A.ι))
    (hB : IsEssentiallyConstantPro (G ⋙ restrictBoundedCoherentLift B.ι)) :
    IsEssentiallyConstantPro ((G ⋙ (boundedCoherentDerived Y).ι) ⋙
      Stacks.Cohomology.RestrictionCover.derivedCoverMiddle Y.ringCatSheaf
        (derivedExtensionRestriction Y.ringCatSheaf A)
        (derivedExtensionRestriction Y.ringCatSheaf B)) := by
  let G' := G ⋙ (boundedCoherentDerived Y).ι
  let DA := derivedExtensionRestriction Y.ringCatSheaf A
  let DB := derivedExtensionRestriction Y.ringCatSheaf B
  let Q := Stacks.Cohomology.RestrictionCover.derivedCoverMiddle Y.ringCatSheaf DA DB
  let inl : G' ⋙ DA ⟶ G' ⋙ Q :=
    { app n := biprod.inl
      naturality n m f := by
        show DA.map (G'.map f) ≫ biprod.inl =
          biprod.inl ≫ biprod.map (DA.map (G'.map f)) (DB.map (G'.map f))
        simp }
  let snd : G' ⋙ Q ⟶ G' ⋙ DB :=
    { app n := biprod.snd
      naturality n m f := by
        show biprod.map (DA.map (G'.map f)) (DB.map (G'.map f)) ≫ biprod.snd =
          biprod.snd ≫ DB.map (G'.map f)
        simp }
  exact isEssentiallyConstantPro_of_split inl snd
    (fun _ => binaryBiproductTriangle_distinguished _ _)
    (isEssentiallyConstantPro_derivedExtensionRestriction A G hA)
    (isEssentiallyConstantPro_derivedExtensionRestriction B G hB)

/-- An inverse system in `D^b_{Coh}(𝒪_Y)` which is essentially constant in `D(𝒪_Y)` is
essentially constant: its value is a retract of a term of the system, hence lies in
`D^b_{Coh}(𝒪_Y)`. -/
private lemma isEssentiallyConstantPro_of_comp_ι [IsLocallyNoetherian Y]
    (G : ℕᵒᵖ ⥤ BoundedCoherentDerived Y)
    (h : IsEssentiallyConstantPro (G ⋙ (boundedCoherentDerived Y).ι)) :
    IsEssentiallyConstantPro G := by
  obtain ⟨c, i, s, hs⟩ := h
  have hpt : boundedCoherentDerived Y c.pt :=
    (DerivedCategoryB.derivedCategoryBBounded_isStableUnderRetracts _
      (Stacks.AlgebraicGeometry.ProperSupportCoherent.isCoherent_isWeakSerre Y)).of_retract
      ⟨c.π.app i, s, hs.retraction⟩ (G.obj i).property
  exact IsEssentiallyConstantPro.of_comp_fullyFaithful (boundedCoherentDerived Y).fullyFaithfulι
    hs (Y := ⟨c.pt, hpt⟩) (Iso.refl _)

/-- **Essential constancy in `D^b_{Coh}` is local for a cover by two opens.** Let `Y` be a
locally Noetherian scheme covered by two opens `A` and `B`, and let `(K_n)` be an inverse system
in `D^b_{Coh}(𝒪_Y)`. If `(K_n|_A)`, `(K_n|_B)` and `(K_n|_{A ∩ B})` are essentially constant
pro-objects, then so is `(K_n)`.

The natural Mayer--Vietoris triangles of Stacks 08BU and Stacks 0G3A give essential constancy in
`D(𝒪_Y)`; the value is a retract of a term of the system, hence lies in `D^b_{Coh}(𝒪_Y)`. This is
the step of the proof of [Stacks, Tag 0G4T] showing that the restriction to `U` is essentially
constant. -/
public theorem isEssentiallyConstantPro_of_cover [IsLocallyNoetherian Y]
    (A B : Y.Opens) (hAB : A ⊔ B = ⊤) (G : ℕᵒᵖ ⥤ BoundedCoherentDerived Y)
    (hA : IsEssentiallyConstantPro (G ⋙ restrictBoundedCoherentLift A.ι))
    (hB : IsEssentiallyConstantPro (G ⋙ restrictBoundedCoherentLift B.ι))
    (hAB' : IsEssentiallyConstantPro (G ⋙ restrictBoundedCoherentLift (A ⊓ B).ι)) :
    IsEssentiallyConstantPro G := by
  let O := Y.ringCatSheaf
  let G' := G ⋙ (boundedCoherentDerived Y).ι
  let DA := derivedExtensionRestriction O A
  let DB := derivedExtensionRestriction O B
  let DAB := derivedExtensionRestriction O (A ⊓ B)
  obtain ⟨iA, iB, δ, -, -, hT⟩ := distinguished_extensionRestriction_triangle O A B hAB
    DA DB DAB (derivedExtensionRestrictionFactorsh O A).inv
    (derivedExtensionRestrictionFactorsh O B).inv
    (derivedExtensionRestrictionFactorsh O (A ⊓ B)).inv
  let cA := derivedExtensionRestrictionCounit O A DA (derivedExtensionRestrictionFactorsh O A).inv
  let cB := derivedExtensionRestrictionCounit O B DB (derivedExtensionRestrictionFactorsh O B).inv
  let Q := Stacks.Cohomology.RestrictionCover.derivedCoverMiddle O DA DB
  let a : DAB ⟶ Q :=
    { app E := biprod.lift (iA.app E) (iB.app E)
      naturality E E' f := by
        show DAB.map f ≫ biprod.lift (iA.app E') (iB.app E') =
          biprod.lift (iA.app E) (iB.app E) ≫ biprod.map (DA.map f) (DB.map f)
        refine biprod.hom_ext _ _ ?_ ?_
        · simp only [Category.assoc, biprod.lift_fst, biprod.lift_map]
          exact iA.naturality f
        · simp only [Category.assoc, biprod.lift_snd, biprod.lift_map]
          exact iB.naturality f }
  let b : Q ⟶ 𝟭 _ :=
    { app E := biprod.desc (cA.app E) (cB.app E)
      naturality E E' f := by
        show biprod.map (DA.map f) (DB.map f) ≫ biprod.desc (cA.app E') (cB.app E') =
          biprod.desc (cA.app E) (cB.app E) ≫ f
        refine biprod.hom_ext' _ _ ?_ ?_
        · simp only [biprod.inl_map_assoc, biprod.inl_desc_assoc, biprod.inl_desc]
          exact cA.naturality f
        · simp only [biprod.inr_map_assoc, biprod.inr_desc_assoc, biprod.inr_desc]
          exact cB.naturality f }
  -- the Mayer--Vietoris triangles and Stacks 0G3A give essential constancy in `D(𝒪_Y)`
  exact isEssentiallyConstantPro_of_comp_ι G
    (isEssentiallyConstantPro_of_natTriangle a b δ hT G'
      (isEssentiallyConstantPro_derivedExtensionRestriction (A ⊓ B) G hAB')
      (isEssentiallyConstantPro_derivedCoverMiddle A B G hA hB))

end AlgebraicGeometry

end
