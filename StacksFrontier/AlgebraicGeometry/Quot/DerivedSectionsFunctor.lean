module

public import StacksFrontier.AlgebraicGeometry.Quot.PerfectOfVanishingPullbacks
public import StacksFrontier.AlgebraicGeometry.Quot.LeftDerivedPullbackData
public import StacksFrontier.AlgebraicGeometry.Quot.DegreeZeroSectionsRepresentable
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents

/-!
# Stacks 08JX, part (2): the functor `T ↦ H⁰(T, Lg^*K)`

Let `K` be a pseudo-coherent object of `D(𝒪_X)` on an algebraic space `X` such that
`Hⁱ(Lg^*K) = 0` for every scheme `g : T → X` and every `i < 0`.  Then the functor
`(g : T → X) ↦ H⁰(T, Lg^*K) = Hom_{D(𝒪_T)}(𝒪_T, Lg^*K)` is the degree-zero sections functor of
part (1) (the source's "under the assumptions of (2) we have `H⁰(T, Lg^*K) = H⁰(T, H⁰(Lg^*K))`"),
hence an algebraic space affine and of finite presentation over `X`.

## Main results

* `Space.isAffineFinitePresentationSectionFunctor_of_hasVanishingNegativeDerivedPullback`:
  Stacks 08JX, part (2), the conclusion about the functor `T ↦ H⁰(T, Lg^*K)`.  The two
  conclusions about `K` itself are
  `Space.isPerfect_and_locally_hasTorAmplitude_of_hasVanishingNegativeDerivedPullback`.
* `AlgebraicGeometry.Space.derivedPullbackSectionFunctorIso`: under the hypothesis of part (2),
  the functor `T ↦ H⁰(T, Lg^*K)` is the degree-zero sections functor of part (1).
* `CategoryTheory.PullbackData.relKerFunctorIsoDerivedRelHom`: for a right exact pullback datum
  and a complex `P₀` whose pullbacks have no negative cohomology, the degree-zero kernel functor
  of `P₀` is the relative Hom functor of the left derived datum out of `O[0]`.
* `CategoryTheory.PullbackData.relKerTransportIso`: the relative kernel functor of a transported
  pullback datum.
* `CategoryTheory.PullbackData.leftDerived_relHomMap_conj`: restriction in the relative Hom
  functor of a left derived datum, read through the comparisons with the underived datum.

## References

* [Stacks Project, Tag 08JX](https://stacks.math.columbia.edu/tag/08JX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat)

namespace CategoryTheory.PullbackData

/-! ### The relative kernel functor of a transported datum -/

section Transport

variable {A : Type*} [Category* A] {D : A → Type*} [∀ a, Category* (D a)] [∀ a, Abelian (D a)]
  (P : PullbackData A D) [∀ {a b : A} (f : a ⟶ b), (P.pull f).PreservesZeroMorphisms]
  (pull' : ∀ {a b : A}, (a ⟶ b) → (D b ⥤ D a)) (ε : ∀ {a b : A} (f : a ⟶ b), pull' f ≅ P.pull f)
  [∀ {a b : A} (f : a ⟶ b), (pull' f).PreservesZeroMorphisms]
  {I : Type*} [Category* I] {π : I ⥤ A} {a₀ : A}

omit [∀ a, Abelian (D a)] [∀ {a b : A} (f : a ⟶ b), (P.pull f).PreservesZeroMorphisms]
  [∀ {a b : A} (f : a ⟶ b), (pull' f).PreservesZeroMorphisms] in
/-- Conjugating along the comparison of a transported datum is conjugating along the comparison
of the original datum, read through the transporting isomorphisms. -/
theorem conjHom_transport_triangle {a b d : A} {f : a ⟶ b} {g : b ⟶ d} {k : a ⟶ d}
    (hk : f ≫ g = k) {M N : D d} (α : (pull' g).obj M ⟶ (pull' g).obj N) :
    (ε k).inv.app M ≫ Functor.conjHom ((P.transport pull' ε).triangle hk) α ≫ (ε k).hom.app N =
      Functor.conjHom (P.triangle hk) ((ε g).inv.app M ≫ α ≫ (ε g).hom.app N) := by
  rw [transport_triangle]
  simp only [Functor.conjHom, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp]
  have n := (ε f).hom.naturality α
  rw [Iso.inv_hom_id_app, Category.comp_id, reassoc_of% n, Iso.inv_hom_id_app_assoc]

/-- **The relative kernel functor of a transported datum** is that of the original datum: a
morphism killed by the transported inverse image is carried, by the transporting isomorphisms,
to one killed by the original inverse image. -/
def relKerTransportIso (hP : P.IsCoherent) (κ : ConeTo π a₀) (M : D a₀) {N N' : D a₀}
    (φ : N ⟶ N') :
    (P.transport pull' ε).relKerFunctor (transport_isCoherent P pull' ε hP) κ M φ ≅
      P.relKerFunctor hP κ M φ :=
  NatIso.ofComponents
    (fun i =>
      { hom := ↾fun α => ⟨(ε (κ.leg i.unop)).inv.app M ≫ α.1 ≫ (ε (κ.leg i.unop)).hom.app N, by
          rw [Category.assoc, Category.assoc, ← (ε (κ.leg i.unop)).hom.naturality φ,
            ← Category.assoc α.1, α.2, zero_comp, comp_zero]⟩
        inv := ↾fun α => ⟨(ε (κ.leg i.unop)).hom.app M ≫ α.1 ≫ (ε (κ.leg i.unop)).inv.app N, by
          rw [Category.assoc, Category.assoc, ← (ε (κ.leg i.unop)).inv.naturality φ,
            ← Category.assoc α.1, α.2, zero_comp, comp_zero]⟩
        hom_inv_id := ConcreteCategory.hom_ext _ _ fun α => Subtype.ext (by
          change (ε (κ.leg i.unop)).hom.app M ≫ ((ε (κ.leg i.unop)).inv.app M ≫ α.1 ≫
            (ε (κ.leg i.unop)).hom.app N) ≫ (ε (κ.leg i.unop)).inv.app N = α.1
          simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
            Iso.hom_inv_id_app_assoc])
        inv_hom_id := ConcreteCategory.hom_ext _ _ fun α => Subtype.ext (by
          change (ε (κ.leg i.unop)).inv.app M ≫ ((ε (κ.leg i.unop)).hom.app M ≫ α.1 ≫
            (ε (κ.leg i.unop)).inv.app N) ≫ (ε (κ.leg i.unop)).hom.app N = α.1
          simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
            Iso.inv_hom_id_app_assoc]) })
    (fun {i j} g => ConcreteCategory.hom_ext _ _ fun α => Subtype.ext
      (P.conjHom_transport_triangle pull' ε (κ.w g.unop) α.1))

end Transport

/-! ### Restriction in the relative Hom functor of a left derived datum -/

section LeftDerived

universe v₁ u₁ v₂ u₂ v₃ u₃

variable {A : Type u₁} [Category.{v₁} A] {H : A → Type u₂} [∀ a, Category.{v₂} (H a)]
  {D : A → Type u₃} [∀ a, Category.{v₃} (D a)]
  (Q : ∀ a, H a ⥤ D a) (W : ∀ a, MorphismProperty (H a)) [∀ a, (Q a).IsLocalization (W a)]
  (P : PullbackData A H) (L : ∀ {a b : A}, (a ⟶ b) → (D b ⥤ D a))
  (c : ∀ {a b : A} (f : a ⟶ b), Q b ⋙ L f ⟶ P.pull f ⋙ Q a)
  [hL : ∀ {a b : A} (f : a ⟶ b), (L f).IsLeftDerivedFunctor (c f) (W b)]
  [hcomp : ∀ {a b d : A} (f : a ⟶ b) (g : b ⟶ d), IsIso (derivedComp Q W P L c f g)]
  [hid : ∀ a : A, IsIso (derivedIdLift Q W P L c a)]

/-- The comparison of the left derived datum along a presented composite, read through the
comparisons, at an object at which the comparisons are invertible. -/
theorem leftDerived_triangle_hom_app_eq {a b d : A} {f : a ⟶ b} {g : b ⟶ d} {k : a ⟶ d}
    (hk : f ≫ g = k) (X : H d) [IsIso ((c k).app X)] [IsIso ((c g).app X)]
    [IsIso ((c f).app ((P.pull g).obj X))] :
    ((leftDerived Q W P L c).triangle hk).hom.app ((Q d).obj X) =
      (c k).app X ≫ (Q a).map ((P.triangle hk).hom.app X) ≫ inv ((c f).app ((P.pull g).obj X)) ≫
        (L f).map (inv ((c g).app X)) := by
  have h := leftDerived_triangle_inv_fac Q W P L c hk X
  have h' : ((leftDerived Q W P L c).triangle hk).inv.app ((Q d).obj X) ≫ ((c k).app X ≫
      (Q a).map ((P.triangle hk).hom.app X) ≫ inv ((c f).app ((P.pull g).obj X)) ≫
        (L f).map (inv ((c g).app X))) = 𝟙 _ := by
    rw [reassoc_of% h, ← (Q a).map_comp_assoc, Iso.inv_hom_id_app]
    simp
  calc ((leftDerived Q W P L c).triangle hk).hom.app ((Q d).obj X)
      = ((leftDerived Q W P L c).triangle hk).hom.app ((Q d).obj X) ≫
          (((leftDerived Q W P L c).triangle hk).inv.app ((Q d).obj X) ≫ ((c k).app X ≫
            (Q a).map ((P.triangle hk).hom.app X) ≫ inv ((c f).app ((P.pull g).obj X)) ≫
              (L f).map (inv ((c g).app X)))) := by rw [h', Category.comp_id]
    _ = _ := by rw [Iso.hom_inv_id_app_assoc]

variable {I : Type*} [Category* I] {π : I ⥤ A} {a₀ : A}

/-- **Restriction in the relative Hom functor of a left derived datum, read through the
comparisons with the underived datum**: conjugating by the comparisons at the two objects, the
restriction of `α` along `g` is the left derived functor of `π g` applied to the conjugate of `α`,
conjugated by the comparisons at the inverse images and by the underived comparison of the
triangle. -/
theorem leftDerived_relHomMap_conj (κ : ConeTo π a₀) (M N : H a₀) {j i : I} (g : j ⟶ i)
    [IsIso ((c (κ.leg i)).app M)] [IsIso ((c (κ.leg i)).app N)] [IsIso ((c (κ.leg j)).app M)]
    [IsIso ((c (κ.leg j)).app N)] [IsIso ((c (π.map g)).app ((P.pull (κ.leg i)).obj M))]
    [IsIso ((c (π.map g)).app ((P.pull (κ.leg i)).obj N))]
    (α : (L (κ.leg i)).obj ((Q a₀).obj M) ⟶ (L (κ.leg i)).obj ((Q a₀).obj N)) :
    inv ((c (κ.leg j)).app M) ≫ (leftDerived Q W P L c).relHomMap κ ((Q a₀).obj M)
        ((Q a₀).obj N) g α ≫ (c (κ.leg j)).app N =
      (Q _).map ((P.triangle (κ.w g)).hom.app M) ≫ inv ((c (π.map g)).app _) ≫
        (L (π.map g)).map (inv ((c (κ.leg i)).app M) ≫ α ≫ (c (κ.leg i)).app N) ≫
          (c (π.map g)).app _ ≫ (Q _).map ((P.triangle (κ.w g)).inv.app N) := by
  change inv ((c (κ.leg j)).app M) ≫ (((leftDerived Q W P L c).triangle (κ.w g)).hom.app _ ≫
    (L (π.map g)).map α ≫ ((leftDerived Q W P L c).triangle (κ.w g)).inv.app _) ≫
      (c (κ.leg j)).app N = _
  rw [leftDerived_triangle_hom_app_eq Q W P L c (κ.w g) M]
  have h := leftDerived_triangle_inv_fac Q W P L c (κ.w g) N
  simp only [Category.assoc, IsIso.inv_hom_id_assoc, h, Functor.map_comp]

end LeftDerived


/-! ### The relative Hom functor along isomorphisms of its two objects -/

section RelHomIso

variable {A : Type*} [Category* A] {D : A → Type*} [∀ a, Category* (D a)] (P : PullbackData A D)
  {I : Type*} [Category* I] {π : I ⥤ A} {a₀ : A}

/-- **The relative Hom functor along isomorphisms of its two objects.** -/
def relHomFunctorIso (hP : P.IsCoherent) (κ : ConeTo π a₀) {M M' N N' : D a₀} (a : M ≅ M')
    (b : N ≅ N') : P.relHomFunctor hP κ M N ≅ P.relHomFunctor hP κ M' N' where
  hom := P.relHomBimap hP κ a.inv b.hom
  inv := P.relHomBimap hP κ a.hom b.inv
  hom_inv_id := by
    ext i α
    change (P.pull (κ.leg i.unop)).map a.hom ≫ ((P.pull (κ.leg i.unop)).map a.inv ≫ α ≫
      (P.pull (κ.leg i.unop)).map b.hom) ≫ (P.pull (κ.leg i.unop)).map b.inv = α
    simp only [Category.assoc, Iso.hom_inv_id_map_assoc]
    exact (Category.assoc _ _ _).trans ((congrArg (α ≫ ·)
      ((P.pull (κ.leg i.unop)).mapIso b).hom_inv_id).trans (Category.comp_id α))
  inv_hom_id := by
    ext i α
    change (P.pull (κ.leg i.unop)).map a.inv ≫ ((P.pull (κ.leg i.unop)).map a.hom ≫ α ≫
      (P.pull (κ.leg i.unop)).map b.inv) ≫ (P.pull (κ.leg i.unop)).map b.hom = α
    simp only [Category.assoc, Iso.inv_hom_id_map_assoc]
    exact (Category.assoc _ _ _).trans ((congrArg (α ≫ ·)
      ((P.pull (κ.leg i.unop)).mapIso b).inv_hom_id).trans (Category.comp_id α))

end RelHomIso

end CategoryTheory.PullbackData

/-! ### Morphisms out of a single object into a complex concentrated in degrees `≥ 0` -/

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- **Morphisms in `D(C)` from `A[0]` to a complex `Z` concentrated in degrees `≥ 0` are the
morphisms of complexes**, that is the morphisms `A ⟶ Z⁰` killed by the differential. -/
theorem bijective_Q_map_mkHomFromSingle (A : C) (Z : CochainComplex C ℤ) [Z.IsStrictlyGE 0] :
    Function.Bijective (fun t : {t : A ⟶ Z.X 0 // t ≫ Z.d 0 1 = 0} =>
      Q.map (HomologicalComplex.mkHomFromSingle (c := ComplexShape.up ℤ) (j := 0) t.1
        (fun k hk => by
          obtain rfl : k = 1 := by simpa using hk.symm
          exact t.2))) := by
  have hZ : (Q.obj Z).IsGE 0 := inferInstance
  -- `H⁰` is bijective on the morphisms out of `A[0]` into an object concentrated in degrees `≥ 0`
  have hH : Function.Bijective (fun β : Q.obj ((HomologicalComplex.single C (ComplexShape.up ℤ)
      0).obj A) ⟶ Q.obj Z => (homologyFunctor C 0).map β) := by
    have h := bijective_homologyFromSingle_of_isGE A (Q.obj Z) 0
    have key : (fun β : Q.obj ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj A) ⟶
        Q.obj Z => (homologyFunctor C 0).map β) =
        (fun k => ((singleFunctorCompHomologyFunctorIso C 0).app A).hom ≫ k) ∘
          (homologyFromSingle A (Q.obj Z) 0 : _ → _) := by
      funext β
      simp only [Function.comp_apply, homologyFromSingle_apply, Iso.app_hom,
        ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    rw [key]
    exact ((Iso.homFromEquiv
      ((singleFunctorCompHomologyFunctorIso C 0).app A).symm).bijective).comp h
  have hπ : IsIso (Z.homologyπ 0) := Z.isIso_homologyπ (-1) 0 (by simp)
    ((Z.isZero_of_isStrictlyGE 0 (-1) (by omega)).eq_of_src _ _)
  -- the identifications of `H⁰` of the two objects with the cohomology of the complexes
  let eS : (homologyFunctor C 0).obj (Q.obj ((HomologicalComplex.single C (ComplexShape.up ℤ)
      0).obj A)) ≅ ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj A).homology 0 :=
    (homologyFunctorFactors C 0).app _
  let eZ : (homologyFunctor C 0).obj (Q.obj Z) ≅ Z.homology 0 := (homologyFunctorFactors C 0).app Z
  have hcomp : ∀ t : {t : A ⟶ Z.X 0 // t ≫ Z.d 0 1 = 0},
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 A).inv ≫ eS.inv ≫
        (homologyFunctor C 0).map (Q.map (HomologicalComplex.mkHomFromSingle
          (c := ComplexShape.up ℤ) (j := 0) t.1 (fun k hk => by
            obtain rfl : k = 1 := by simpa using hk.symm
            exact t.2))) ≫ eZ.hom =
      Z.liftCycles t.1 1 (by simp) t.2 ≫ Z.homologyπ 0 := by
    intro t
    have n : (homologyFunctor C 0).map (Q.map (HomologicalComplex.mkHomFromSingle
        (c := ComplexShape.up ℤ) (j := 0) t.1 (fun k hk => by
          obtain rfl : k = 1 := by simpa using hk.symm
          exact t.2))) ≫ eZ.hom = eS.hom ≫ HomologicalComplex.homologyMap
        (HomologicalComplex.mkHomFromSingle (c := ComplexShape.up ℤ) (j := 0) t.1
          (fun k hk => by
            obtain rfl : k = 1 := by simpa using hk.symm
            exact t.2)) 0 :=
      (homologyFunctorFactors C 0).hom.naturality _
    rw [n, Iso.inv_hom_id_assoc,
      ← HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ_assoc,
      HomologicalComplex.homologyπ_naturality, ← Category.assoc]
    refine congrArg (· ≫ Z.homologyπ 0) ?_
    rw [← cancel_mono (Z.iCycles 0), Category.assoc, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.liftCycles_i, HomologicalComplex.mkHomFromSingle_f,
      HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles_assoc, Iso.inv_hom_id_assoc]
  -- the map `t ↦ liftCycles t ≫ homologyπ` is bijective
  have hlift : Function.Bijective (fun t : {t : A ⟶ Z.X 0 // t ≫ Z.d 0 1 = 0} =>
      Z.liftCycles t.1 1 (by simp) t.2 ≫ Z.homologyπ 0) := by
    refine ⟨fun t₁ t₂ h => Subtype.ext ?_, fun u => ?_⟩
    · have h' := (cancel_mono (Z.homologyπ 0)).1 h
      have := congrArg (· ≫ Z.iCycles 0) h'
      simpa using this
    · refine ⟨⟨u ≫ inv (Z.homologyπ 0) ≫ Z.iCycles 0, by simp⟩, ?_⟩
      have hl : Z.liftCycles (u ≫ inv (Z.homologyπ 0) ≫ Z.iCycles 0) 1 (by simp) (by simp) =
          u ≫ inv (Z.homologyπ 0) := by
        rw [← cancel_mono (Z.iCycles 0), HomologicalComplex.liftCycles_i, Category.assoc]
      change Z.liftCycles (u ≫ inv (Z.homologyπ 0) ≫ Z.iCycles 0) 1 _ _ ≫ Z.homologyπ 0 = u
      rw [hl, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  -- conclude
  have key : (fun t : {t : A ⟶ Z.X 0 // t ≫ Z.d 0 1 = 0} =>
      Z.liftCycles t.1 1 (by simp) t.2 ≫ Z.homologyπ 0) =
      (Iso.homCongr
        (eS ≪≫ HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 A) eZ) ∘
        (fun β => (homologyFunctor C 0).map β) ∘
        (fun t : {t : A ⟶ Z.X 0 // t ≫ Z.d 0 1 = 0} =>
          Q.map (HomologicalComplex.mkHomFromSingle (c := ComplexShape.up ℤ) (j := 0) t.1
            (fun k hk => by
              obtain rfl : k = 1 := by simpa using hk.symm
              exact t.2))) := by
    funext t
    simpa [Iso.homCongr] using (hcomp t).symm
  rw [key] at hlift
  exact (Function.Bijective.of_comp_iff' hH _).1
    ((Function.Bijective.of_comp_iff' (Equiv.bijective _) _).1 hlift)

/-- `DerivedCategory.bijective_Q_map_mkHomFromSingle` read through the homotopy category. -/
theorem bijective_Qh_map_mkHomFromSingle (A : C) (Z : CochainComplex C ℤ) [Z.IsStrictlyGE 0] :
    Function.Bijective (fun t : {t : A ⟶ Z.X 0 // t ≫ Z.d 0 1 = 0} =>
      Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        (HomologicalComplex.mkHomFromSingle (c := ComplexShape.up ℤ) (j := 0) t.1
          (fun k hk => by
            obtain rfl : k = 1 := by simpa using hk.symm
            exact t.2)))) := by
  have key : (fun t : {t : A ⟶ Z.X 0 // t ≫ Z.d 0 1 = 0} =>
      Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        (HomologicalComplex.mkHomFromSingle (c := ComplexShape.up ℤ) (j := 0) t.1
          (fun k hk => by
            obtain rfl : k = 1 := by simpa using hk.symm
            exact t.2)))) =
      (fun β => ((quotientCompQhIso C).app _).hom ≫ β ≫ ((quotientCompQhIso C).app Z).inv) ∘
        (fun t : {t : A ⟶ Z.X 0 // t ≫ Z.d 0 1 = 0} =>
          Q.map (HomologicalComplex.mkHomFromSingle (c := ComplexShape.up ℤ) (j := 0) t.1
            (fun k hk => by
              obtain rfl : k = 1 := by simpa using hk.symm
              exact t.2))) := by
    funext t
    simp only [Function.comp_apply, Iso.app_hom, Iso.app_inv]
    rw [← (quotientCompQhIso C).hom.naturality_assoc, Iso.hom_inv_id_app, Category.comp_id]
    rfl
  rw [key]
  exact (Iso.homCongr ((quotientCompQhIso C).app _).symm
    ((quotientCompQhIso C).app Z).symm).bijective.comp (bijective_Q_map_mkHomFromSingle A Z)

end DerivedCategory


/-! ### The canonical truncation in degrees `≥ 0` under a right exact functor -/

namespace CochainComplex

variable {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]

/-- The degree-zero component of the projection onto the canonical truncation in degrees
`≥ 0`. -/
theorem πTruncGE_f_zero (Y : CochainComplex C ℤ) :
    (Y.πTruncGE 0).f 0 = Y.pOpcycles 0 ≫ (Y.truncGEXIsoOpcycles 0).inv := by
  change ((ComplexShape.embeddingUpIntGE 0).liftExtend
    (Y.restrictionToTruncGE' (ComplexShape.embeddingUpIntGE 0))
    (Y.restrictionToTruncGE'_hasLift (ComplexShape.embeddingUpIntGE 0))).f 0 = _
  have h0 : (ComplexShape.embeddingUpIntGE 0).f 0 = 0 := by simp
  rw [(ComplexShape.embeddingUpIntGE 0).liftExtend_f _ _ h0,
    Y.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv (ComplexShape.embeddingUpIntGE 0) h0
      (by rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff])]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- The differential of the canonical truncation in degrees `≥ 0` out of degree `0`, read through
the identification of its degree-zero term with the opcycles: it is the map from the opcycles to
the next term. -/
theorem truncGE_d_zero_one (Y : CochainComplex C ℤ) :
    (Y.truncGE 0).d 0 1 = (Y.truncGEXIsoOpcycles 0).hom ≫ Y.fromOpcycles 0 1 ≫
      (Y.πTruncGE 0).f 1 := by
  have h := (Y.πTruncGE 0).comm 0 1
  rw [πTruncGE_f_zero, ← Y.p_fromOpcycles 0 1, Category.assoc, Category.assoc] at h
  have h' := (cancel_epi (Y.pOpcycles 0)).1 h
  rw [← h', Iso.hom_inv_id_assoc]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]

include F in
/-- **The projection onto the canonical truncation in degrees `≥ 0` stays a quasi-isomorphism
after a right exact functor**, as soon as the image of the complex has no cohomology in negative
degrees: the functor carries the degree-zero opcycles to the degree-zero opcycles. -/
theorem quasiIso_map_πTruncGE (Y : CochainComplex C ℤ)
    (hY : CochainComplex.IsGE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Y) 0) :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (Y.πTruncGE 0)) := by
  let G := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let φ := G.map (Y.πTruncGE 0)
  have hF : F.PreservesEpimorphisms := inferInstance
  have hpos : ∀ j : ℤ, 0 < j → IsIso (φ.f j) := fun j hj => by
    have := Y.isIso_πTruncGE_f_of_lt 0 j hj
    change IsIso (F.map ((Y.πTruncGE 0).f j))
    infer_instance
  have hzero : Epi (φ.f 0) := by
    have : Epi ((Y.πTruncGE 0).f 0) :=
      inferInstanceAs (Epi ((HomologicalComplex.πTruncGE Y (ComplexShape.embeddingUpIntGE 0)).f 0))
    change Epi (F.map ((Y.πTruncGE 0).f 0))
    infer_instance
  have hZneg : ∀ j : ℤ, j < 0 → IsZero ((G.obj (Y.truncGE 0)).X j) := fun j hj =>
    F.map_isZero ((Y.truncGE 0).isZero_of_isStrictlyGE 0 j hj)
  rw [quasiIso_iff]
  intro i
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · -- negative degrees: both sides have zero cohomology
    have := hY
    rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_of_isGE (G.obj Y) 0 i hi)]
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (G.obj (Y.truncGE 0)).isZero_homology_of_isZero_X i (hZneg i hi)
  · -- degree zero: the opcycles agree and the next differential is unchanged
    rw [quasiIsoAt_iff_isIso_homologyMap]
    have hp : IsIso ((G.obj (Y.truncGE 0)).pOpcycles 0) :=
      (G.obj (Y.truncGE 0)).isIso_pOpcycles (-1) 0 (by simp) ((hZneg (-1) (by omega)).eq_of_src _ _)
    let m := Y.mapOpcyclesIsoOfPreservesCokernel F (-1) 0 (by norm_num)
    have hm : HomologicalComplex.opcyclesMap φ 0 =
        m.inv ≫ F.map (Y.truncGEXIsoOpcycles 0).inv ≫ (G.obj (Y.truncGE 0)).pOpcycles 0 := by
      have := Y.epi_map_pOpcycles F (-1) 0 (by norm_num)
      rw [← cancel_epi ((G.obj Y).pOpcycles 0), HomologicalComplex.p_opcyclesMap,
        ← HomologicalComplex.map_pOpcycles_mapOpcyclesIso_hom_assoc (K := Y) F (-1) 0 (by norm_num),
        Iso.hom_inv_id_assoc, ← F.map_comp_assoc]
      change F.map ((Y.πTruncGE 0).f 0) ≫ _ = _
      rw [πTruncGE_f_zero]
    have hiso : IsIso (HomologicalComplex.opcyclesMap φ 0) := by
      rw [hm]; infer_instance
    have hmono :
        Mono (((HomologicalComplex.shortComplexFunctor D (ComplexShape.up ℤ) 0).map φ).τ₃) := by
      change Mono (φ.f ((ComplexShape.up ℤ).next 0))
      have := hpos ((ComplexShape.up ℤ).next 0) (by simp)
      infer_instance
    exact ShortComplex.isIso_homologyMap_of_isIso_opcyclesMap_of_mono hiso hmono
  · -- positive degrees: the three terms are isomorphic or the first is an epimorphism
    rw [quasiIsoAt_iff' _ (i - 1) i (i + 1) (by simp) (by simp)]
    have h₂ : IsIso (((HomologicalComplex.shortComplexFunctor' D (ComplexShape.up ℤ) (i - 1) i
        (i + 1)).map φ).τ₂) := hpos i hi
    have h₃ : IsIso (((HomologicalComplex.shortComplexFunctor' D (ComplexShape.up ℤ) (i - 1) i
        (i + 1)).map φ).τ₃) := hpos (i + 1) (by omega)
    have h₁ : Epi (((HomologicalComplex.shortComplexFunctor' D (ComplexShape.up ℤ) (i - 1) i
        (i + 1)).map φ).τ₁) := by
      change Epi (φ.f (i - 1))
      rcases eq_or_lt_of_le (show 0 ≤ i - 1 by omega) with h | h
      · rw [← h]; exact hzero
      · have := hpos (i - 1) h; exact IsIso.epi_of_iso (φ.f (i - 1))
    exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono _

end CochainComplex

/-! ### The comparison `F(H⁰(K)) ⟶ H⁰(F(K))` for a right exact functor -/

namespace HomologicalComplex

variable {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]

/-- **The comparison of degree-zero cohomology along a right exact functor**,
`F(H⁰(K)) ⟶ H⁰(F(K))`: the image of the inclusion of `H⁰(K)` into the opcycles, followed by the
identification of the opcycles of `F(K)` with the image of those of `K`, factors through the
kernel `H⁰(F(K))` of the map to the next term. -/
noncomputable def homologyZeroComparison (K : CochainComplex C ℤ) :
    F.obj (K.homology 0) ⟶ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology 0 :=
  ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homToHomologyEquiv 0 1 (by norm_num) _
    ⟨F.map (K.homologyι 0) ≫ (K.mapOpcyclesIsoOfPreservesCokernel F (-1) 0 (by norm_num)).hom, by
      rw [Category.assoc, mapOpcyclesIso_hom_fromOpcycles, ← F.map_comp,
        homologyι_comp_fromOpcycles, F.map_zero]⟩

/-- The comparison `F(H⁰(K)) ⟶ H⁰(F(K))` followed by the inclusion of `H⁰(F(K))` into the
opcycles is the image of the inclusion of `H⁰(K)`, followed by the identification of the opcycles
of `F(K)` with the image of those of `K`. -/
@[reassoc (attr := simp)]
theorem homologyZeroComparison_homologyι (K : CochainComplex C ℤ) :
    homologyZeroComparison F K ≫ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyι 0 =
      F.map (K.homologyι 0) ≫ (K.mapOpcyclesIsoOfPreservesCokernel F (-1) 0 (by norm_num)).hom :=
  homToHomologyEquiv_apply_comp _ _ _ _ _ _

/-- The comparison of degree-zero cohomology is natural in the complex. -/
@[reassoc]
theorem homologyZeroComparison_naturality {K K' : CochainComplex C ℤ} (φ : K ⟶ K') :
    homologyZeroComparison F K ≫
        homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) 0 =
      F.map (homologyMap φ 0) ≫ homologyZeroComparison F K' := by
  rw [← cancel_mono (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K').homologyι 0),
    Category.assoc, homologyι_naturality, homologyZeroComparison_homologyι_assoc,
    Category.assoc, homologyZeroComparison_homologyι, ← map_opcyclesMap_mapOpcyclesIso_hom,
    ← F.map_comp_assoc, ← F.map_comp_assoc, homologyι_naturality]

end HomologicalComplex

/-! ### The relative Hom functor of the left derived datum out of a single object -/

namespace CategoryTheory.PullbackData

section DerivedSections

universe v₁ u₁ v₂ u₂

variable {A : Type u₁} [Category.{v₁} A] {M : A → Type u₂} [∀ a, Category.{v₂} (M a)]
  [∀ a, Abelian (M a)] [∀ a, HasDerivedCategory.{v₂} (M a)]
  (P : PullbackData A M) [hadd : ∀ {a b : A} (f : a ⟶ b), (P.pull f).Additive]
  [hrex : ∀ {a b : A} (f : a ⟶ b), PreservesFiniteColimits (P.pull f)]
  (L : ∀ {a b : A}, (a ⟶ b) → (DerivedCategory (M b) ⥤ DerivedCategory (M a)))
  (c : ∀ {a b : A} (f : a ⟶ b),
    DerivedCategory.Qh ⋙ L f ⟶ (P.toHomotopy).pull f ⋙ DerivedCategory.Qh)
  [hL : ∀ {a b : A} (f : a ⟶ b),
    (L f).IsLeftDerivedFunctor (c f) (HomotopyCategory.quasiIso (M b) (ComplexShape.up ℤ))]
  [hcomp : ∀ {a b d : A} (f : a ⟶ b) (g : b ⟶ d),
    IsIso (derivedComp (fun _ => DerivedCategory.Qh)
      (fun a => HomotopyCategory.quasiIso (M a) (ComplexShape.up ℤ)) P.toHomotopy L c f g)]
  [hid : ∀ a : A, IsIso (derivedIdLift (fun _ => DerivedCategory.Qh)
      (fun a => HomotopyCategory.quasiIso (M a) (ComplexShape.up ℤ)) P.toHomotopy L c a)]

/-- The left derived datum of `P` on the derived categories. -/
abbrev derivedDatum : PullbackData A (fun a => DerivedCategory (M a)) :=
  leftDerived (fun _ => DerivedCategory.Qh)
    (fun a => HomotopyCategory.quasiIso (M a) (ComplexShape.up ℤ)) P.toHomotopy L c

variable {I : Type*} [Category* I] {π : I ⥤ A} {a₀ : A} (κ : ConeTo π a₀) (O : M a₀)
  (P₀ : CochainComplex (M a₀) ℤ)

/-- The cycles of degree zero of the pullback of the truncation `τ_{≥ 0}P₀` attached to a
section of the relative kernel functor of the map from the opcycles of `P₀` to its next term. -/
def truncCycleOf (i : I) (s : P.relKerObj κ O (P₀.fromOpcycles 0 1) i) :
    {t : (P.pull (κ.leg i)).obj O ⟶
        (((P.pull (κ.leg i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj (P₀.truncGE 0)).X 0 //
      t ≫ (((P.pull (κ.leg i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (P₀.truncGE 0)).d 0 1 = 0} :=
  ⟨s.1 ≫ (P.pull (κ.leg i)).map (P₀.truncGEXIsoOpcycles 0).inv, by
    change (s.1 ≫ (P.pull (κ.leg i)).map (P₀.truncGEXIsoOpcycles 0).inv) ≫
      (P.pull (κ.leg i)).map ((P₀.truncGE 0).d 0 1) = 0
    rw [CochainComplex.truncGE_d_zero_one, Category.assoc, ← Functor.map_comp,
      Iso.inv_hom_id_assoc, Functor.map_comp, ← Category.assoc, s.2, zero_comp]⟩

omit [∀ a, HasDerivedCategory.{v₂} (M a)] hrex in
/-- The underlying morphism of `truncCycleOf` is the section followed by the pullback of the
identification of the opcycles of `P₀` with the degree-zero term of `τ_{≥ 0}P₀`. -/
theorem truncCycleOf_coe (i : I) (s : P.relKerObj κ O (P₀.fromOpcycles 0 1) i) :
    (P.truncCycleOf κ O P₀ i s).1 = s.1 ≫ (P.pull (κ.leg i)).map (P₀.truncGEXIsoOpcycles 0).inv :=
  rfl

/-- The section of the relative kernel functor attached to the cycles of degree zero of the
pullback of the truncation `τ_{≥ 0}P₀`: the inverse of `truncCycleOf`. -/
def ofTruncCycle (i : I)
    (t : {t : (P.pull (κ.leg i)).obj O ⟶
        (((P.pull (κ.leg i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj (P₀.truncGE 0)).X 0 //
      t ≫ (((P.pull (κ.leg i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (P₀.truncGE 0)).d 0 1 = 0}) :
    P.relKerObj κ O (P₀.fromOpcycles 0 1) i :=
  ⟨t.1 ≫ (P.pull (κ.leg i)).map (P₀.truncGEXIsoOpcycles 0).hom, by
    have : IsIso ((P₀.πTruncGE 0).f 1) := P₀.isIso_πTruncGE_f_of_lt 0 1 (by norm_num)
    have h : t.1 ≫ (P.pull (κ.leg i)).map ((P₀.truncGE 0).d 0 1) = 0 := t.2
    rw [CochainComplex.truncGE_d_zero_one, Functor.map_comp, Functor.map_comp] at h
    rw [Category.assoc, ← cancel_mono ((P.pull (κ.leg i)).map ((P₀.πTruncGE 0).f 1)),
      Category.assoc, zero_comp]
    simpa only [Category.assoc] using h⟩

/-- `truncCycleOf` is a bijection. -/
def truncCycleEquiv (i : I) :
    P.relKerObj κ O (P₀.fromOpcycles 0 1) i ≃
      {t : (P.pull (κ.leg i)).obj O ⟶
        (((P.pull (κ.leg i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj (P₀.truncGE 0)).X 0 //
      t ≫ (((P.pull (κ.leg i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (P₀.truncGE 0)).d 0 1 = 0} where
  toFun := P.truncCycleOf κ O P₀ i
  invFun := P.ofTruncCycle κ O P₀ i
  left_inv s := Subtype.ext (by
    change (s.1 ≫ (P.pull (κ.leg i)).map (P₀.truncGEXIsoOpcycles 0).inv) ≫
      (P.pull (κ.leg i)).map (P₀.truncGEXIsoOpcycles 0).hom = s.1
    rw [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id]
    exact Category.comp_id _)
  right_inv t := Subtype.ext (by
    change (t.1 ≫ (P.pull (κ.leg i)).map (P₀.truncGEXIsoOpcycles 0).hom) ≫
      (P.pull (κ.leg i)).map (P₀.truncGEXIsoOpcycles 0).inv = t.1
    rw [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, Functor.map_id]
    exact Category.comp_id _)

/-- The morphism of complexes from the pullback of `O[0]` to the pullback of `τ_{≥ 0}P₀` attached
to a section of the relative kernel functor. -/
def truncChainOf (i : I) (s : P.relKerObj κ O (P₀.fromOpcycles 0 1) i) :
    ((P.pull (κ.leg i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (M a₀) (ComplexShape.up ℤ) 0).obj O) ⟶
      ((P.pull (κ.leg i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj (P₀.truncGE 0) :=
  (HomologicalComplex.singleMapHomologicalComplex (P.pull (κ.leg i))
      (ComplexShape.up ℤ) 0).hom.app O ≫
    HomologicalComplex.mkHomFromSingle (c := ComplexShape.up ℤ) (j := 0)
      (P.truncCycleOf κ O P₀ i s).1 (fun k hk => by
        obtain rfl : k = 1 := by simpa using hk.symm
        exact (P.truncCycleOf κ O P₀ i s).2)

omit [∀ a, HasDerivedCategory.{v₂} (M a)] hrex in
/-- The pullback of the truncation `τ_{≥ 0}P₀` is concentrated in degrees `≥ 0`. -/
theorem isStrictlyGE_pull_truncGE {a : A} (f : a ⟶ a₀) :
    CochainComplex.IsStrictlyGE
      (((P.pull f).mapHomologicalComplex (ComplexShape.up ℤ)).obj (P₀.truncGE 0)) 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact (P.pull f).map_isZero ((P₀.truncGE 0).isZero_of_isStrictlyGE 0 i hi)

/-- The projection onto the truncation, pulled back along `f`. -/
abbrev pullπ {a : A} (f : a ⟶ a₀) :=
  ((P.pull f).mapHomologicalComplex (ComplexShape.up ℤ)).map (P₀.πTruncGE 0)

omit [∀ a, HasDerivedCategory.{v₂} (M a)] hrex in
/-- **The morphism of complexes attached to a restricted section** is the conjugate, by the
comparison of the triangle, of the image of the morphism attached to the section. -/
theorem truncChainOf_relKerMap (hP : P.IsCoherent) {j i : I} (g : j ⟶ i)
    (s : P.relKerObj κ O (P₀.fromOpcycles 0 1) i) :
    P.truncChainOf κ O P₀ j ((P.relKerFunctor hP κ O (P₀.fromOpcycles 0 1)).map g.op s) =
      (NatTrans.mapHomologicalComplex (P.triangle (κ.w g)).hom (ComplexShape.up ℤ)).app
          ((HomologicalComplex.single (M a₀) (ComplexShape.up ℤ) 0).obj O) ≫
        ((P.pull (π.map g)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (P.truncChainOf κ O P₀ i s) ≫
        (NatTrans.mapHomologicalComplex (P.triangle (κ.w g)).inv (ComplexShape.up ℤ)).app
          (P₀.truncGE 0) := by
  ext k
  by_cases hk : k = 0
  · subst hk
    simp only [truncChainOf, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.mkHomFromSingle_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self, Category.assoc,
      Iso.inv_hom_id_assoc, Functor.map_comp, truncCycleOf_coe]
    change _ ≫ Functor.conjHom (P.triangle (κ.w g)) s.1 ≫ _ = _
    simp only [Functor.conjHom, Category.assoc]
    have n₁ := (P.triangle (κ.w g)).hom.naturality
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 O).hom
    have n₂ := (P.triangle (κ.w g)).inv.naturality (P₀.truncGEXIsoOpcycles 0).inv
    simp only [Functor.comp_map] at n₁ n₂
    rw [reassoc_of% n₁, ← (P.pull (π.map g)).map_comp_assoc (HomologicalComplex.singleObjXSelf
      (ComplexShape.up ℤ) 0 ((P.pull (κ.leg i)).obj O)).inv, Iso.inv_hom_id, Functor.map_id,
      Category.id_comp, n₂]
  · exact (((P.pull (κ.leg j)).map_isZero
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ hk))).eq_of_src _ _

variable (hge : ∀ i : I,
  CochainComplex.IsGE (((P.pull (κ.leg i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P₀) 0)

include hge in
/-- When the pullbacks of `P₀` have no cohomology in negative degrees, the pullback of the
projection onto the truncation `τ_{≥ 0}P₀` is invertible in the derived category. -/
theorem isIso_Qh_map_pullπ (i : I) :
    IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ _).map (P.pullπ P₀ (κ.leg i)))) := by
  have := CochainComplex.quasiIso_map_πTruncGE (P.pull (κ.leg i)) P₀ (hge i)
  rw [DerivedCategory.isIso_Qh_map_iff]
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 this

/-- **The derived morphism attached to a section of the degree-zero kernel functor**: the
morphism of complexes into the truncation, followed by the inverse of the projection onto the
truncation. -/
noncomputable def sectionsToDerived (i : I) (s : P.relKerObj κ O (P₀.fromOpcycles 0 1) i) :
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
        (((P.pull (κ.leg i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single (M a₀) (ComplexShape.up ℤ) 0).obj O))) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
        (((P.pull (κ.leg i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P₀)) :=
  haveI := P.isIso_Qh_map_pullπ κ P₀ hge i
  DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map (P.truncChainOf κ O P₀ i s)) ≫
    inv (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map (P.pullπ P₀ (κ.leg i))))

/-- `sectionsToDerived` is a bijection from the sections of the degree-zero kernel functor to the
derived morphisms from the pullback of `O[0]` to the pullback of `P₀`. -/
theorem bijective_sectionsToDerived (i : I) :
    Function.Bijective (P.sectionsToDerived κ O P₀ hge i) := by
  have := P.isIso_Qh_map_pullπ κ P₀ hge i
  have := P.isStrictlyGE_pull_truncGE P₀ (κ.leg i)
  let e := DerivedCategory.Qh.mapIso ((HomotopyCategory.quotient _ _).mapIso
    ((HomologicalComplex.singleMapHomologicalComplex (P.pull (κ.leg i))
      (ComplexShape.up ℤ) 0).app O))
  have key : P.sectionsToDerived κ O P₀ hge i =
      (fun β => e.hom ≫ β ≫ inv (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        (P.pullπ P₀ (κ.leg i))))) ∘
        (fun t : {t : (P.pull (κ.leg i)).obj O ⟶
            (((P.pull (κ.leg i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (P₀.truncGE 0)).X 0 //
          t ≫ (((P.pull (κ.leg i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (P₀.truncGE 0)).d 0 1 = 0} =>
          DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
            (HomologicalComplex.mkHomFromSingle (c := ComplexShape.up ℤ) (j := 0) t.1
              (fun k hk => by
                obtain rfl : k = 1 := by simpa using hk.symm
                exact t.2)))) ∘ (P.truncCycleEquiv κ O P₀ i) := by
    funext s
    simp only [Function.comp_apply, sectionsToDerived, truncChainOf, e, Functor.mapIso_hom,
      Iso.app_hom, Functor.map_comp, Category.assoc]
    rfl
  rw [key]
  exact ((Iso.homCongr e.symm (asIso (DerivedCategory.Qh.map
    ((HomotopyCategory.quotient _ _).map (P.pullπ P₀ (κ.leg i))))).symm).bijective).comp
    ((DerivedCategory.bijective_Qh_map_mkHomFromSingle _ _).comp (Equiv.bijective _))


omit [∀ a, HasDerivedCategory.{v₂} (M a)] hrex in
/-- The comparison of the datum on homotopy categories along a presented composite, at the image
of a complex `K`, is the image of the comparison of `P` applied termwise to `K`. -/
theorem toHomotopy_triangle_hom_app' {a b d : A} {f : a ⟶ b} {g : b ⟶ d} {k : a ⟶ d}
    (hk : f ≫ g = k) (K : CochainComplex (M d) ℤ) :
    ((toHomotopy P).triangle hk).hom.app ((HomotopyCategory.quotient (M d) _).obj K) =
      (HomotopyCategory.quotient (M a) _).map
        ((NatTrans.mapHomologicalComplex (P.triangle hk).hom _).app K) := by
  subst hk
  rw [triangle_rfl, triangle_rfl]
  exact (Category.comp_id _).trans rfl

omit hL hrex hcomp hid in
/-- The comparison of the left derived functors, applied to the image of a morphism of
complexes: naturality of the comparison. -/
@[reassoc]
theorem comparison_naturality {a b : A} (f : a ⟶ b) {K K' : CochainComplex (M b) ℤ} (x : K ⟶ K') :
    (L f).map (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map x)) ≫
        (c f).app ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).obj K') =
      (c f).app ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient (M a) (ComplexShape.up ℤ)).map
          (((P.pull f).mapHomologicalComplex (ComplexShape.up ℤ)).map x)) :=
  (c f).naturality ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map x)

omit hL hrex hcomp hid in
/-- **The left derived functor on a roof of complexes**, read through the comparisons: for
morphisms of complexes `x : K ⟶ Y` and `p : K' ⟶ Y` with `p` invertible in the derived
category, after `L f` and the comparisons at `K` and `K'`, the roof `x ≫ p⁻¹` becomes the roof
`f^*x ≫ (f^*p)⁻¹`, as soon as `f^*p` is invertible in the derived category. -/
theorem comparison_conj_roof {a b : A} (f : a ⟶ b) {K K' Y : CochainComplex (M b) ℤ}
    (x : K ⟶ Y) (p : K' ⟶ Y)
    (hp : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map p)))
    (hfp : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient (M a) (ComplexShape.up ℤ)).map
      (((P.pull f).mapHomologicalComplex (ComplexShape.up ℤ)).map p))))
    (hK : IsIso ((c f).app ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).obj K)))
    (hK' : IsIso ((c f).app ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).obj K'))) :
    @inv _ _ _ _ ((c f).app ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).obj K)) hK ≫
        (L f).map (DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map x) ≫
          @inv _ _ _ _ (DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map p)) hp) ≫
        (c f).app ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).obj K') =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient (M a) (ComplexShape.up ℤ)).map
          (((P.pull f).mapHomologicalComplex (ComplexShape.up ℤ)).map x)) ≫
        @inv _ _ _ _ (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (M a) (ComplexShape.up ℤ)).map
            (((P.pull f).mapHomologicalComplex (ComplexShape.up ℤ)).map p))) hfp := by
  have := hp
  have := hK
  have := hK'
  have n₁ := comparison_naturality P L c f x
  have n₂ := comparison_naturality P L c f p
  have := hfp
  refine (@IsIso.eq_comp_inv _ _ _ _ _ _ hfp _ _).2 ?_
  have e : (L f).map (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map x) ≫
      inv (DerivedCategory.Qh.map ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map p))) ≫
        (c f).app ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).obj K') ≫
          DerivedCategory.Qh.map ((HomotopyCategory.quotient (M a) (ComplexShape.up ℤ)).map
            (((P.pull f).mapHomologicalComplex (ComplexShape.up ℤ)).map p)) =
      (c f).app ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient (M a) (ComplexShape.up ℤ)).map
          (((P.pull f).mapHomologicalComplex (ComplexShape.up ℤ)).map x)) := by
    refine (congrArg (fun k => (L f).map (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map x) ≫
        inv (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map p))) ≫ k)
      n₂.symm).trans ?_
    refine Eq.trans ?_ n₁
    have h3 : (L f).map (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map x) ≫
          inv (DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map p))) ≫
        (L f).map (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map p)) =
        (L f).map (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map x)) := by
      rw [← Functor.map_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (c f).app ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).obj Y)) h3)
  calc (inv ((c f).app ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).obj K)) ≫
        (L f).map (DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map x) ≫
          inv (DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map p))) ≫
        (c f).app ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).obj K')) ≫
          DerivedCategory.Qh.map ((HomotopyCategory.quotient (M a) (ComplexShape.up ℤ)).map
            (((P.pull f).mapHomologicalComplex (ComplexShape.up ℤ)).map p))
      = inv ((c f).app ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).obj K)) ≫
        ((L f).map (DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map x) ≫
          inv (DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map p))) ≫
        (c f).app ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).obj K') ≫
          DerivedCategory.Qh.map ((HomotopyCategory.quotient (M a) (ComplexShape.up ℤ)).map
            (((P.pull f).mapHomologicalComplex (ComplexShape.up ℤ)).map p))) := by
        simp only [Category.assoc]
    _ = _ := by
        rw [e, IsIso.inv_hom_id_assoc]
        rfl


include hge in
/-- **Restriction in the relative Hom functor of the left derived datum, on the derived
morphisms attached to sections of the degree-zero kernel functor.** -/
theorem relHomMap_sectionsToDerived (hP : P.IsCoherent) {j i : I} (g : j ⟶ i)
    (s : P.relKerObj κ O (P₀.fromOpcycles 0 1) i)
    (h₁ : IsIso ((c (κ.leg i)).app ((HomotopyCategory.quotient (M a₀) (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single (M a₀) (ComplexShape.up ℤ) 0).obj O))))
    (h₂ : IsIso ((c (κ.leg i)).app ((HomotopyCategory.quotient (M a₀) (ComplexShape.up ℤ)).obj P₀)))
    (h₃ : IsIso ((c (κ.leg j)).app ((HomotopyCategory.quotient (M a₀) (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single (M a₀) (ComplexShape.up ℤ) 0).obj O))))
    (h₄ : IsIso ((c (κ.leg j)).app ((HomotopyCategory.quotient (M a₀) (ComplexShape.up ℤ)).obj P₀)))
    (h₅ : IsIso ((c (π.map g)).app ((P.toHomotopy.pull (κ.leg i)).obj
      ((HomotopyCategory.quotient (M a₀) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (M a₀) (ComplexShape.up ℤ) 0).obj O)))))
    (h₆ : IsIso ((c (π.map g)).app ((P.toHomotopy.pull (κ.leg i)).obj
      ((HomotopyCategory.quotient (M a₀) (ComplexShape.up ℤ)).obj P₀)))) :
    @inv _ _ _ _ ((c (κ.leg j)).app ((HomotopyCategory.quotient (M a₀) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (M a₀) (ComplexShape.up ℤ) 0).obj O))) h₃ ≫
      (P.derivedDatum L c).relHomMap κ _ _ g
        ((c (κ.leg i)).app ((HomotopyCategory.quotient (M a₀) (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single (M a₀) (ComplexShape.up ℤ) 0).obj O)) ≫
          P.sectionsToDerived κ O P₀ hge i s ≫
            @inv _ _ _ _ ((c (κ.leg i)).app ((HomotopyCategory.quotient (M a₀)
              (ComplexShape.up ℤ)).obj P₀)) h₂) ≫
        (c (κ.leg j)).app ((HomotopyCategory.quotient (M a₀) (ComplexShape.up ℤ)).obj P₀) =
      P.sectionsToDerived κ O P₀ hge j
        ((P.relKerFunctor hP κ O (P₀.fromOpcycles 0 1)).map g.op s) := by
  rw [leftDerived_relHomMap_conj]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  have := P.isIso_Qh_map_pullπ κ P₀ hge j
  have := P.isIso_Qh_map_pullπ κ P₀ hge i
  -- the pullback along `π g` of the projection onto the truncation is invertible
  have nπ :=
    (NatTrans.mapHomologicalComplex (P.triangle (κ.w g)).inv (ComplexShape.up ℤ)).naturality
      (P₀.πTruncGE 0)
  have hfp : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      (((P.pull (π.map g)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (P.pullπ P₀ (κ.leg i))))) := by
    have e : DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (((P.pull (π.map g)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (P.pullπ P₀ (κ.leg i)))) =
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((NatIso.mapHomologicalComplex (P.triangle (κ.w g)) (ComplexShape.up ℤ)).app P₀).inv) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          (P.pullπ P₀ (κ.leg j))) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((NatIso.mapHomologicalComplex (P.triangle (κ.w g)) (ComplexShape.up ℤ)).app
            (P₀.truncGE 0)).hom) := by
      simp only [← Functor.map_comp]
      congr 2
      have := (NatIso.mapHomologicalComplex (P.triangle (κ.w g)) (ComplexShape.up ℤ)).hom.naturality
        (P₀.πTruncGE 0)
      rw [Iso.app_hom]
      change _ = _ ≫ (((P.pull (κ.leg j)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (P₀.πTruncGE 0) ≫ _)
      rw [this, Iso.app_inv, Iso.inv_hom_id_app_assoc]
      rfl
    rw [e]
    infer_instance
  -- the roof `χ_i ≫ π_i⁻¹` through the comparisons along `π g`
  have hroof := P.comparison_conj_roof L c (π.map g) (P.truncChainOf κ O P₀ i s)
    (P.pullπ P₀ (κ.leg i)) (P.isIso_Qh_map_pullπ κ P₀ hge i) hfp h₅ h₆
  have eB : DerivedCategory.Qh.map ((P.toHomotopy.triangle (κ.w g)).inv.app
      ((HomotopyCategory.quotient (M a₀) (ComplexShape.up ℤ)).obj P₀)) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (P.pullπ P₀ (κ.leg j))) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (((P.pull (π.map g)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (P.pullπ P₀ (κ.leg i)))) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (P.triangle (κ.w g)).inv (ComplexShape.up ℤ)).app
          (P₀.truncGE 0))) := by
    rw [toHomotopy_triangle_inv_app]
    have := congrArg (fun x => DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map x)) nπ.symm
    simp only [Functor.map_comp] at this ⊢
    exact this
  have eR : P.sectionsToDerived κ O P₀ hge j
      ((P.relKerFunctor hP κ O (P₀.fromOpcycles 0 1)).map g.op s) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (P.pullπ P₀ (κ.leg j))) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (P.truncChainOf κ O P₀ j ((P.relKerFunctor hP κ O (P₀.fromOpcycles 0 1)).map g.op s))) := by
    simp [sectionsToDerived]
  have eA := toHomotopy_triangle_hom_app' P (κ.w g)
    ((HomologicalComplex.single (M a₀) (ComplexShape.up ℤ) 0).obj O)
  have hσ : (P.sectionsToDerived κ O P₀ hge i s ≫
      @inv _ _ _ _ ((c (κ.leg i)).app ((HomotopyCategory.quotient (M a₀) (ComplexShape.up ℤ)).obj
        P₀)) h₂) ≫
        (c (κ.leg i)).app ((HomotopyCategory.quotient (M a₀) (ComplexShape.up ℤ)).obj P₀) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (P.truncChainOf κ O P₀ i s)) ≫
        inv (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          (P.pullπ P₀ (κ.leg i)))) :=
    (Category.assoc _ _ _).trans ((congrArg (P.sectionsToDerived κ O P₀ hge i s ≫ ·)
      (@IsIso.inv_hom_id _ _ _ _ _ h₂)).trans (Category.comp_id _))
  refine (congrArg (fun y => DerivedCategory.Qh.map ((P.toHomotopy.triangle (κ.w g)).hom.app
      ((HomotopyCategory.quotient (M a₀) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (M a₀) (ComplexShape.up ℤ) 0).obj O))) ≫
      @inv _ _ _ _ ((c (π.map g)).app ((P.toHomotopy.pull (κ.leg i)).obj
        ((HomotopyCategory.quotient (M a₀) (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single (M a₀) (ComplexShape.up ℤ) 0).obj O)))) h₅ ≫
      (L (π.map g)).map y ≫
      (c (π.map g)).app ((P.toHomotopy.pull (κ.leg i)).obj
        ((HomotopyCategory.quotient (M a₀) (ComplexShape.up ℤ)).obj P₀)) ≫
      DerivedCategory.Qh.map ((P.toHomotopy.triangle (κ.w g)).inv.app
        ((HomotopyCategory.quotient (M a₀) (ComplexShape.up ℤ)).obj P₀))) hσ).trans ?_
  have hroof' := congrArg (fun y => DerivedCategory.Qh.map ((P.toHomotopy.triangle (κ.w g)).hom.app
      ((HomotopyCategory.quotient (M a₀) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (M a₀) (ComplexShape.up ℤ) 0).obj O))) ≫ y ≫
      DerivedCategory.Qh.map ((P.toHomotopy.triangle (κ.w g)).inv.app
        ((HomotopyCategory.quotient (M a₀) (ComplexShape.up ℤ)).obj P₀))) hroof
  have reassoc₁ : ∀ {X₁ X₂ X₃ X₄ X₅ X₆ : DerivedCategory (M (π.obj j))} (t : X₁ ⟶ X₂)
      (a : X₂ ⟶ X₃) (b : X₃ ⟶ X₄) (c' : X₄ ⟶ X₅) (u : X₅ ⟶ X₆),
      t ≫ a ≫ b ≫ c' ≫ u = t ≫ (a ≫ b ≫ c') ≫ u := by
    intros; simp only [Category.assoc]
  refine (reassoc₁ _ _ _ _ _).trans (hroof'.trans ?_)
  have cancel₁ : ∀ {X₁ X₂ X₃ X₄ X₅ X₆ X₇ : DerivedCategory (M (π.obj j))} (t : X₁ ⟶ X₂)
      (x : X₂ ⟶ X₃) (p : X₄ ⟶ X₃) [IsIso p] (u : X₄ ⟶ X₅) (q : X₅ ⟶ X₆) (b : X₃ ⟶ X₆),
      u ≫ q = p ≫ b → (t ≫ (x ≫ inv p) ≫ u) ≫ q = t ≫ x ≫ b := by
    intro X₁ X₂ X₃ X₄ X₅ X₆ X₇ t x p _ u q b h
    simp only [Category.assoc, h, IsIso.inv_hom_id_assoc]
  refine (cancel_mono (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
    (P.pullπ P₀ (κ.leg j))))).1 ?_
  refine Eq.trans ?_ eR.symm
  refine (@cancel₁ _ _ _ _ _ _ (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _
      (ComplexShape.up ℤ)).obj (((P.pull (κ.leg j)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        P₀))) _ _ _ hfp _ _ _ eB).trans ?_
  rw [eA, truncChainOf_relKerMap P κ O P₀ hP g s]
  simp only [Functor.map_comp]
  rfl


variable (hcX : ∀ i : I, IsIso ((c (κ.leg i)).app ((HomotopyCategory.quotient (M a₀)
    (ComplexShape.up ℤ)).obj ((HomologicalComplex.single (M a₀) (ComplexShape.up ℤ) 0).obj O))))
  (hcY : ∀ i : I, IsIso ((c (κ.leg i)).app
    ((HomotopyCategory.quotient (M a₀) (ComplexShape.up ℤ)).obj P₀)))

/-- The section of the relative Hom functor of the left derived datum attached to a section of
the degree-zero kernel functor. -/
noncomputable def sectionsToRelHom (i : I) (s : P.relKerObj κ O (P₀.fromOpcycles 0 1) i) :
    (P.derivedDatum L c).relHomObj κ (DerivedCategory.Qh.obj ((HomotopyCategory.quotient (M a₀)
      (ComplexShape.up ℤ)).obj ((HomologicalComplex.single (M a₀) (ComplexShape.up ℤ) 0).obj O)))
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient (M a₀) (ComplexShape.up ℤ)).obj P₀)) i :=
  (c (κ.leg i)).app ((HomotopyCategory.quotient (M a₀) (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single (M a₀) (ComplexShape.up ℤ) 0).obj O)) ≫
    P.sectionsToDerived κ O P₀ hge i s ≫
      @inv _ _ _ _ ((c (κ.leg i)).app ((HomotopyCategory.quotient (M a₀) (ComplexShape.up ℤ)).obj
        P₀)) (hcY i)

include hcX in
/-- `sectionsToRelHom` is a bijection from the sections of the degree-zero kernel functor to the
sections of the relative Hom functor of the left derived datum out of `O[0]`. -/
theorem bijective_sectionsToRelHom (i : I) :
    Function.Bijective (P.sectionsToRelHom L c κ O P₀ hge hcY i) := by
  have := hcX i
  have := hcY i
  have key : P.sectionsToRelHom L c κ O P₀ hge hcY i =
      (fun β => (c (κ.leg i)).app ((HomotopyCategory.quotient (M a₀) (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single (M a₀) (ComplexShape.up ℤ) 0).obj O)) ≫ β ≫
        inv ((c (κ.leg i)).app ((HomotopyCategory.quotient (M a₀) (ComplexShape.up ℤ)).obj P₀))) ∘
        P.sectionsToDerived κ O P₀ hge i := rfl
  rw [key]
  refine Function.Bijective.comp ?_ (P.bijective_sectionsToDerived κ O P₀ hge i)
  exact (Iso.homCongr (asIso ((c (κ.leg i)).app ((HomotopyCategory.quotient (M a₀)
    (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single (M a₀) (ComplexShape.up ℤ) 0).obj O)))).symm
    (asIso ((c (κ.leg i)).app ((HomotopyCategory.quotient (M a₀)
      (ComplexShape.up ℤ)).obj P₀))).symm).bijective


variable (hcX' : ∀ {j i : I} (g : j ⟶ i),
    IsIso ((c (π.map g)).app ((P.toHomotopy.pull (κ.leg i)).obj
      ((HomotopyCategory.quotient (M a₀) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (M a₀) (ComplexShape.up ℤ) 0).obj O)))))
  (hcY' : ∀ {j i : I} (g : j ⟶ i), IsIso ((c (π.map g)).app ((P.toHomotopy.pull (κ.leg i)).obj
    ((HomotopyCategory.quotient (M a₀) (ComplexShape.up ℤ)).obj P₀))))

include hcX hcX' hcY' in
/-- **The degree-zero sections functor is the relative Hom functor of the left derived datum out
of `O[0]`**, when the pullbacks of `P₀` have no cohomology in negative degrees and the
comparisons of the derived inverse images are invertible at `O[0]`, at `P₀` and at their
pullbacks. -/
noncomputable def relKerFunctorIsoDerivedRelHom (hP : P.IsCoherent) :
    P.relKerFunctor hP κ O (P₀.fromOpcycles 0 1) ≅
      (P.derivedDatum L c).relHomFunctor
        (leftDerived_isCoherent _ _ _ _ _ (toHomotopy_isCoherent P hP)) κ
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient (M a₀) (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single (M a₀) (ComplexShape.up ℤ) 0).obj O)))
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient (M a₀) (ComplexShape.up ℤ)).obj P₀)) :=
  NatIso.ofComponents
    (fun i => (Equiv.ofBijective _ (P.bijective_sectionsToRelHom L c κ O P₀ hge hcX hcY
      i.unop)).toIso)
    (fun {i j} g => by
      refine ConcreteCategory.hom_ext _ _ fun s => ?_
      change P.sectionsToRelHom L c κ O P₀ hge hcY j.unop
          ((P.relKerFunctor hP κ O (P₀.fromOpcycles 0 1)).map g s) =
        (P.derivedDatum L c).relHomMap κ _ _ g.unop (P.sectionsToRelHom L c κ O P₀ hge hcY i.unop s)
      have h := P.relHomMap_sectionsToDerived L c κ O P₀ hge hP g.unop s (hcX i.unop) (hcY i.unop)
        (hcX j.unop) (hcY j.unop) (hcX' g.unop) (hcY' g.unop)
      have cancel : ∀ {X Y X' Y' : DerivedCategory (M (π.obj j.unop))} (a : X ⟶ X') (_ : IsIso a)
          (b : Y ⟶ Y') (_ : IsIso b) (r : X ⟶ Y), a ≫ (inv a ≫ r ≫ b) ≫ inv b = r := by
        intro X Y X' Y' a _ b _ r
        simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id, IsIso.hom_inv_id_assoc]
      exact (congrArg (fun t => (c (κ.leg j.unop)).app ((HomotopyCategory.quotient (M a₀)
          (ComplexShape.up ℤ)).obj
            ((HomologicalComplex.single (M a₀) (ComplexShape.up ℤ) 0).obj O)) ≫
          t ≫ @inv _ _ _ _ ((c (κ.leg j.unop)).app ((HomotopyCategory.quotient (M a₀)
            (ComplexShape.up ℤ)).obj P₀)) (hcY j.unop)) h.symm).trans
        (cancel _ (hcX j.unop) _ (hcY j.unop) _))

end DerivedSections

end CategoryTheory.PullbackData

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The inverse image of `𝒪`-modules along the morphism of small étale ringed topoi is right
exact: it is isomorphic to the inverse image of Stacks 03LU, a left adjoint. -/
instance toposPullbackModules_preservesFiniteColimits {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    PreservesFiniteColimits ((toposPullbackData B S hS).pull f) :=
  preservesFiniteColimits_of_natIso (toposPullbackModulesIso f).symm

/-- The derived pullback datum of the small étale ringed topoi is the left derived datum of the
inverse image of modules. -/
example : (derivedPullbackCoherence B S hS).toPullbackData =
    PullbackData.derivedDatum (P := toposPullbackData B S hS)
      (L := fun f => smallEtaleDerivedModulePullback B S hS f)
      (c := fun f => smallEtaleDerivedModulePullbackComparison B S hS f)
      (hL := fun f => isLeftDerivedFunctor_smallEtaleDerivedModulePullback f)
      (hcomp := fun f g => isIso_smallEtaleDerivedComp f g)
      (hid := fun X => isIso_smallEtaleDerivedIdLift X) := rfl

section SectionFunctor

variable {X : AlgebraicSpaces B S hS} (P₀ : CochainComplex (toposModules B S hS X) ℤ)
  (hP₀ : IsKFlat (Y := smallEtaleRingedTopos B S hS X)
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P₀))
  {K : derivedModules B S hS X} {hL : BottomRankStratum.HasDerivedModulePullbacks B S hS}
  (hvan : HasVanishingNegativeDerivedPullback hL K) (e : DerivedCategory.Q.obj P₀ ≅ K)

include hvan hP₀ e in
/-- The pullbacks of a K-flat representative to the schemes over `X` are concentrated in degrees
`≥ 0` under the hypothesis of Stacks 08JX, part (2), for the inverse images of the small étale
ringed topoi. -/
theorem isGE_toposPullback_of_hasVanishingNegative {T : BigFppfOver B S hS}
    (g : (schemeSpaceFunctor B S hS).obj T ⟶ X) :
    CochainComplex.IsGE ((((toposPullbackData B S hS).pull g).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P₀) 0 := by
  have h : CochainComplex.IsGE ((((toposModulePullbackData B S hS).pull g).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P₀) 0 := by
    rw [CochainComplex.isGE_iff]
    intro i hi
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
      (isZero_homology_pull_of_hasVanishingNegative P₀ hP₀ hL hvan e g i hi)
  exact CochainComplex.isGE_of_iso
    ((NatIso.mapHomologicalComplex (toposPullbackModulesIso g) (ComplexShape.up ℤ)).app P₀).symm 0

/-- The algebraic space of a test scheme, in the two spellings of the source of its structure
morphism. -/
theorem schemeSpaceFunctor_obj_left_eq (T : SchemesOver X) :
    (schemeSpaceFunctor B S hS).obj T.left =
      (CostructuredArrow.proj (schemeSpaceFunctor B S hS) X ⋙ schemeSpaceFunctor B S hS).obj T :=
  rfl

include hvan hP₀ e in
/-- `AlgebraicGeometry.Space.isGE_toposPullback_of_hasVanishingNegative` along a morphism whose
source is only equal to the algebraic space of a scheme. -/
theorem isGE_toposPullback_of_eq {T : BigFppfOver B S hS} {Y : AlgebraicSpaces B S hS}
    (hY : (schemeSpaceFunctor B S hS).obj T = Y) (g : Y ⟶ X) :
    CochainComplex.IsGE ((((toposPullbackData B S hS).pull g).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P₀) 0 := by
  subst hY
  exact isGE_toposPullback_of_hasVanishingNegative P₀ hP₀ hvan e g

include hvan hP₀ e in
/-- The pullbacks of a K-flat representative along the structure morphisms of the test schemes
over `X` are concentrated in degrees `≥ 0`, under the hypothesis of Stacks 08JX, part (2). -/
theorem isGE_toposPullback_leg (T : SchemesOver X) :
    CochainComplex.IsGE ((((toposPullbackData B S hS).pull
      ((schemesOverCone X).leg T)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P₀) 0 :=
  isGE_toposPullback_of_eq P₀ hP₀ hvan e (schemeSpaceFunctor_obj_left_eq T)
    ((schemesOverCone X).leg T)

/-- The comparison of the derived inverse image of the small étale ringed topoi is invertible at
the pullback of a K-flat complex. -/
theorem isIso_comparison_app_pull {Y Z W : AlgebraicSpaces B S hS} (f : Y ⟶ Z) (h : Z ⟶ W)
    (L : CochainComplex (toposModules B S hS W) ℤ)
    (hL' : IsKFlat (Y := smallEtaleRingedTopos B S hS W)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)) :
    IsIso ((smallEtaleDerivedModulePullbackComparison B S hS f).app
      (((toposPullbackData B S hS).toHomotopy.pull h).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L))) :=
  isIso_smallEtaleDerivedModulePullbackComparison_app_of_isKFlat f _
    (Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isKFlat_pullbackMapHomotopy
      (smallEtaleRingedToposHom B S hS h) _ hL')

include hvan hP₀ in
/-- **The functor of Stacks 08JX, part (2), is the degree-zero sections functor of part (1)**:
when the pullbacks of `K` to the schemes over `X` have no cohomology in negative degrees,
`H⁰(T, Lg^*K) = Hom_{D(𝒪_T)}(𝒪_T, Lg^*K)` is `H⁰(T, H⁰(Lg^*K))`, naturally in the scheme
`g : T → X`, read on a K-flat representative `P₀` of `K` with flat terms. -/
def derivedPullbackSectionFunctorIso :
    derivedPullbackSectionFunctor (derivedPullbackCoherence B S hS) K ≅
      degreeZeroSectionsFunctor (schemesOverCone X) P₀ :=
  PullbackData.relHomFunctorIso (derivedPullbackCoherence B S hS).toPullbackData
      (derivedPullbackCoherence B S hS).isCoherent (schemesOverCone X)
      ((DerivedCategory.singleFunctorIsoCompQh _ 0).app (SheafOfModules.unit _))
      (e.symm ≪≫ ((DerivedCategory.quotientCompQhIso _).app P₀).symm) ≪≫
    (PullbackData.relKerFunctorIsoDerivedRelHom (P := toposPullbackData B S hS)
      (L := fun f => smallEtaleDerivedModulePullback B S hS f)
      (c := fun f => smallEtaleDerivedModulePullbackComparison B S hS f)
      (hL := fun f => isLeftDerivedFunctor_smallEtaleDerivedModulePullback f)
      (hcomp := fun f g => isIso_smallEtaleDerivedComp f g)
      (hid := fun X => isIso_smallEtaleDerivedIdLift X)
      (schemesOverCone X) (SheafOfModules.unit _) P₀
      (fun T => isGE_toposPullback_leg P₀ hP₀ hvan e T)
      (fun T => isIso_smallEtaleDerivedModulePullbackComparison_app_of_isKFlat
        ((schemesOverCone X).leg T) _
        (Stacks.Cohomology.LerayOfToposHom.isKFlat_single_unit (smallEtaleRingedTopos B S hS X)))
      (fun T => isIso_smallEtaleDerivedModulePullbackComparison_app_of_isKFlat
        ((schemesOverCone X).leg T) _ hP₀)
      (fun {_ T} _ => isIso_comparison_app_pull _ ((schemesOverCone X).leg T) _
        (Stacks.Cohomology.LerayOfToposHom.isKFlat_single_unit (smallEtaleRingedTopos B S hS X)))
      (fun {_ T} _ => isIso_comparison_app_pull _ ((schemesOverCone X).leg T) P₀ hP₀)
      (toposPullbackData_isCoherent B S hS)).symm ≪≫
    PullbackData.relKerTransportIso (toposModulePullbackData B S hS)
      (fun f => (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules)
      (fun f => toposPullbackModulesIso f) (toposModulePullbackData_isCoherent B S hS)
      (schemesOverCone X) (SheafOfModules.unit _) (P₀.fromOpcycles 0 1)

end SectionFunctor

/-- **Stacks 08JX, part (2), the functor.**  Let `K` be a pseudo-coherent object of `D(𝒪_X)` on
an algebraic space `X` such that `Hⁱ(Lg^*K) = 0` for every scheme `g : T → X` and every `i < 0`.
Then the functor `(g : T → X) ↦ H⁰(T, Lg^*K)` on the schemes over `X` is an algebraic space
affine and of finite presentation over `X`.

As in the source, under this hypothesis `H⁰(T, Lg^*K) = H⁰(T, H⁰(Lg^*K))`
(`AlgebraicGeometry.Space.derivedPullbackSectionFunctorIso`), so the statement is part (1). -/
@[stacks 08JX "part (2), the conclusion that `(g : T → B) ↦ H⁰(T, Lg^*K)` is an algebraic \
space affine and of finite presentation over `B`"]
theorem isAffineFinitePresentationSectionFunctor_of_hasVanishingNegativeDerivedPullback
    {X : AlgebraicSpaces B S hS} (K : derivedModules B S hS X) (hK : IsPseudoCoherentObject K)
    (hvan : HasVanishingNegativeDerivedPullback (hasDerivedModulePullbacks B S hS) K) :
    IsAffineFinitePresentationSectionFunctor (derivedPullbackCoherence B S hS) K := by
  obtain ⟨P₀, hP₀, ⟨e⟩⟩ := exists_isKFlat_representative K
  exact IsAffineFinitePresentationAlgebraicSpaceOver.of_iso
    (derivedPullbackSectionFunctorIso P₀ hP₀ hvan e).symm
    (isAffineFinitePresentationAlgebraicSpaceOver_degreeZeroSectionsFunctor K hK
      hvan.hasVanishingDegreeNegOne P₀ hP₀ e)

end AlgebraicGeometry.Space

end
