module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedCoherator.Bound

/-!
# The affine case of the coherator, from an affine derived equivalence

Let `Y` be an algebraic space and let `T : D(R) ⥤ D(𝒪_Y)` be a functor with a right adjoint
`G : D(𝒪_Y) ⥤ D(R)` — for `Y` affine with `R = Γ(Y, 𝒪_Y)`, `T` is induced by `M ↦ M~` and
`G = RΓ(Y, -)`. If `T` is fully faithful (the unit is invertible), lands in `D_QCoh(𝒪_Y)`, is
represented on objects by complexes of quasi-coherent modules and does not raise top degrees, and
if the counit is invertible on `D_QCoh(𝒪_Y)`, then:

* every object `K` of `D(𝒪_Y)` is coreflective, with coreflection `T(G K) ⟶ K`;
* every object of `D_QCoh(𝒪_Y)` is represented by a complex of quasi-coherent modules;
* the coreflection of `K` lies in degrees `≤ b` as soon as `G K` does.

These are the three clauses of `AlgebraicGeometry.Space.AffineCoheratorCase` at `Y`.

## Main results

* `AlgebraicGeometry.Space.rightOrthogonal_obj₃_of_bijective_comp_mor₁`: a triangle whose first
  morphism induces bijections on morphisms out of `P` has its third object right orthogonal to
  `P`.
* `AlgebraicGeometry.Space.affineCoreflection_of_equivalence`: the three clauses.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

section Orthogonal

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- Bijectivity of post-composition with a morphism transports along compatible bijections of
hom-sets. -/
theorem bijective_comp_of_bijective_of_equiv {P X Y P' X' Y' : C} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (a : (P ⟶ X) ≃ (P' ⟶ X')) (b : (P ⟶ Y) ≃ (P' ⟶ Y'))
    (hab : ∀ g : P ⟶ X, a g ≫ f' = b (g ≫ f))
    (h : Function.Bijective fun g : P ⟶ X ↦ g ≫ f) :
    Function.Bijective fun g : P' ⟶ X' ↦ g ≫ f' := by
  have heq : (fun g : P' ⟶ X' ↦ g ≫ f') = b ∘ (fun g : P ⟶ X ↦ g ≫ f) ∘ a.symm := by
    funext g
    simpa using hab (a.symm g)
  rw [heq]
  exact b.bijective.comp (h.comp a.symm.bijective)

omit [HasZeroObject C] [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- Post-composition with `f⟦n⟧'` on morphisms out of `P` is bijective if post-composition with
`f` on morphisms out of `P⟦-n⟧` is. -/
theorem bijective_comp_shift_map {P X Y : C} (f : X ⟶ Y) (n : ℤ)
    (h : Function.Bijective fun g : P⟦-n⟧ ⟶ X ↦ g ≫ f) :
    Function.Bijective fun g : P ⟶ X⟦n⟧ ↦ g ≫ f⟦n⟧' :=
  bijective_comp_of_bijective_of_equiv
    ((shiftEquiv' C (-n) n (neg_add_cancel n)).toAdjunction.homEquiv P X)
    ((shiftEquiv' C (-n) n (neg_add_cancel n)).toAdjunction.homEquiv P Y)
    (fun g ↦ ((shiftEquiv' C (-n) n (neg_add_cancel n)).toAdjunction.homEquiv_naturality_right
      g f).symm) h

/-- If composition with the first morphism of a distinguished triangle is bijective on morphisms
out of every object of a shift-stable `P`, then the third object is right orthogonal to `P`. -/
theorem rightOrthogonal_obj₃_of_bijective_comp_mor₁ (P : ObjectProperty C)
    [P.IsStableUnderShift ℤ] {T : Triangle C} (hT : T ∈ distTriang C)
    (h : ∀ ⦃W : C⦄, P W → Function.Bijective fun g : W ⟶ T.obj₁ ↦ g ≫ T.mor₁) :
    P.rightOrthogonal T.obj₃ := by
  intro W k hW
  have hW' : P (W⟦(-1 : ℤ)⟧) := P.le_shift (-1) W hW
  have h₁ : k ≫ T.mor₃ = 0 := by
    refine (bijective_comp_shift_map T.mor₁ 1 (h hW')).1 ?_
    dsimp only
    rw [zero_comp, Category.assoc, comp_distTriang_mor_zero₃₁ T hT, comp_zero]
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₃ T hT k h₁
  obtain ⟨g', hg'⟩ := (h hW).2 g
  dsimp only at hg'
  rw [hg, ← hg', Category.assoc, comp_distTriang_mor_zero₁₂ T hT, comp_zero]

end Orthogonal

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The affine case of the coherator, from a derived equivalence.** Let `T ⊣ G` with
`T : A ⥤ D(𝒪_Y)`, unit invertible and counit invertible on `D_QCoh(𝒪_Y)`, and suppose `T` lands
in `D_QCoh(𝒪_Y)`, is represented on objects by complexes of quasi-coherent modules and carries
objects `≤ b` (for a given predicate `IsLEA` on `A`) to objects with no cohomology above `b`, and
that `G` of a K-injective complex of affine amplitude at most `b` is `≤ b`. Then every object of
`D(𝒪_Y)` is coreflective, every object of `D_QCoh(𝒪_Y)` is represented by a complex of
quasi-coherent modules, and every K-injective complex of affine amplitude at most `b` has a
decomposition triangle whose first object has no cohomology above `b`. -/
theorem affineCoreflection_of_equivalence (Y : AlgebraicSpaces B S hS)
    {A : Type v} [Category.{w} A] [HasZeroObject A] [HasShift A ℤ] [Preadditive A]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
    (T : A ⥤ spaceDerivedCategory B S hS Y) (G : spaceDerivedCategory B S hS Y ⥤ A)
    (adj : T ⊣ G) [IsIso adj.unit]
    (hcounit : ∀ E, spaceQuasicoherentProp B S hS Y E → IsIso (adj.counit.app E))
    (hTqc : ∀ M, spaceQuasicoherentProp B S hS Y (T.obj M))
    (hTrep : ∀ M, ∃ (C : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ)
      (_ : ∀ n, (C.X n).IsQuasicoherentOnSite), Nonempty ((spaceDerivedQ B S hS Y).obj C ≅ T.obj M))
    (IsLEA : A → ℤ → Prop)
    (hTle : ∀ M b, IsLEA M b → SpaceCohomologyVanishesAbove B S hS Y b (T.obj M))
    (hGamp : ∀ (b : ℤ) (I : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ), I.IsKInjective →
      SectionsAmplitudeLE B S hS Y b I → IsLEA (G.obj ((spaceDerivedQ B S hS Y).obj I)) b) :
    (∀ K, spaceCoreflective B S hS Y K) ∧
    (∀ E, spaceQuasicoherentProp B S hS Y E →
      ∃ (C : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ)
        (_ : ∀ n, (C.X n).IsQuasicoherentOnSite), Nonempty ((spaceDerivedQ B S hS Y).obj C ≅ E)) ∧
    ∀ (b : ℤ) (I : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ), I.IsKInjective →
      SectionsAmplitudeLE B S hS Y b I →
        ∃ (E Q' : spaceDerivedCategory B S hS Y) (a : E ⟶ (spaceDerivedQ B S hS Y).obj I)
          (b' : (spaceDerivedQ B S hS Y).obj I ⟶ Q') (c : Q' ⟶ E⟦(1 : ℤ)⟧),
          Triangle.mk a b' c ∈ distTriang _ ∧ spaceQuasicoherentProp B S hS Y E ∧
            (spaceQuasicoherentProp B S hS Y).rightOrthogonal Q' ∧
            SpaceCohomologyVanishesAbove B S hS Y b E := by
  let P := spaceQuasicoherentProp B S hS Y
  have hGε : ∀ K, IsIso (G.map (adj.counit.app K)) := fun K => by
    have : IsIso (adj.unit.app (G.obj K) ≫ G.map (adj.counit.app K)) := by
      rw [adj.right_triangle_components K]; exact IsIso.id _
    exact IsIso.of_isIso_comp_left (adj.unit.app (G.obj K)) _
  have hN : ∀ (K : spaceDerivedCategory B S hS Y) (N : A),
      Function.Bijective fun g : T.obj N ⟶ T.obj (G.obj K) ↦ g ≫ adj.counit.app K := by
    intro K N
    exact (adj.comp_map_bijective_iff (adj.counit.app K) N).1
      ((isIso_iff_yoneda_map_bijective _).1 (hGε K) N)
  have hbij : ∀ K ⦃W⦄, P W → Function.Bijective fun g : W ⟶ T.obj (G.obj K) ↦
      g ≫ adj.counit.app K := by
    intro K W hW
    have := hcounit W hW
    let eW : T.obj (G.obj W) ≅ W := asIso (adj.counit.app W)
    exact bijective_comp_of_bijective_of_equiv (eW.homCongr (Iso.refl _))
      (eW.homCongr (Iso.refl _)) (fun g ↦ by simp) (hN K (G.obj W))
  have hdec : ∀ K : spaceDerivedCategory B S hS Y, ∃ (Q' : spaceDerivedCategory B S hS Y)
      (b' : K ⟶ Q') (c : Q' ⟶ (T.obj (G.obj K))⟦(1 : ℤ)⟧),
      Triangle.mk (adj.counit.app K) b' c ∈ distTriang _ ∧ P.rightOrthogonal Q' := by
    intro K
    obtain ⟨Q', b', c, hT⟩ := distinguished_cocone_triangle (adj.counit.app K)
    exact ⟨Q', b', c, hT, rightOrthogonal_obj₃_of_bijective_comp_mor₁ P hT (hbij K)⟩
  refine ⟨fun K => ?_, fun E hE => ?_, fun b I hI hamp => ?_⟩
  · obtain ⟨Q', b', c, hT, hQ'⟩ := hdec K
    exact ⟨_, _, _, _, _, hT, hTqc _, hQ'⟩
  · have := hcounit E hE
    obtain ⟨C, hC, ⟨e⟩⟩ := hTrep (G.obj E)
    exact ⟨C, hC, ⟨e ≪≫ asIso (adj.counit.app E)⟩⟩
  · obtain ⟨Q', b', c, hT, hQ'⟩ := hdec ((spaceDerivedQ B S hS Y).obj I)
    exact ⟨_, Q', _, b', c, hT, hTqc _, hQ', hTle _ b (hGamp b I hI hamp)⟩

end AlgebraicGeometry.Space

end
