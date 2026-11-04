module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.Existence.OpenRingMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.SolutionPresentationStalk

/-!
# Solution presentations relative to an open subscheme

`AlgebraicGeometry.SolutionPresentation` describes an object `W` of the small étale site of `S`
whose chart-valued points are the solutions of a polynomial system with coefficients pushed along
a ring map `R ⟶ Γ(S, ⊤)`.  Over a non-affine base the étale charts one can present are those
lying over an affine open `T` of `S`, and their coefficients live in `Γ(T, ⊤)` rather than in
`Γ(S, ⊤)`.  This module is the relative version: an object `W` of the small étale site of `S`
lying over `T`, whose chart-valued points over a chart `U` lying over `T` are the solutions of
the system over `Γ(U, ⊤)` with coefficients pushed along `ψ : R ⟶ Γ(T, ⊤)` and restriction.

It provides the two things the existence half of Stacks 04I7 uses a presentation for, exactly as
for `AlgebraicGeometry.SolutionPresentation`: the universal property of `h_W` among sheaves lying
over `h_T` (`AlgebraicGeometry.RelSolutionPresentation.existsUnique_hom`), and the stalk of `h_W`
at a point of the site lying over `T` as the solutions in the stalk ring
(`AlgebraicGeometry.RelSolutionPresentation.bijective_stalkSolution`).

## References

* [Stacks Project, Tag 04I7](https://stacks.math.columbia.edu/tag/04I7)
* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits

universe u

namespace AlgebraicGeometry

section Coeff

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T : S.Opens)

/-- The object of the small étale site of `S` given by an open `T`. -/
abbrev openObj : SmallEtale B S hS := (opensToBoundedEtale B S hS).obj T

variable {R : Type u} [CommRing R]
  (ψ : R →+* ↥Γ((SmallEtale.toScheme B S hS).obj (openObj B S hS T), ⊤))

/-- The coefficients of the system over a chart lying over `T`. -/
def relCoeff {U : SmallEtale B S hS} (k : U ⟶ openObj B S hS T) :
    R →+* ↥Γ((SmallEtale.toScheme B S hS).obj U, ⊤) :=
  (smallEtaleRestrict B S hS k).comp ψ

/-- Restricting the coefficients over a chart `U` along `j : U' ⟶ U` gives the coefficients
over `U'`. -/
theorem relCoeff_comp {U U' : SmallEtale B S hS} (j : U' ⟶ U) (k : U ⟶ openObj B S hS T) :
    (smallEtaleRestrict B S hS j).comp (relCoeff B S hS T ψ k) = relCoeff B S hS T ψ (j ≫ k) := by
  rw [relCoeff, relCoeff, ← RingHom.comp_assoc]
  congr 1

end Coeff

/-- **A sheaf on the small étale site presented, relative to an open `T`, as the solution sheaf
of a polynomial system.** -/
structure RelSolutionPresentation (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : S.Opens) {R : Type u} [CommRing R]
    (ψ : R →+* ↥Γ((SmallEtale.toScheme B S hS).obj (openObj B S hS T), ⊤)) {n : ℕ}
    (P : Fin n → MvPolynomial (Fin n) R) where
  /-- The presented object of the small étale site. -/
  obj : SmallEtale B S hS
  /-- It lies over `T`. -/
  over : obj ⟶ openObj B S hS T
  /-- Its chart-valued points over a chart lying over `T` are the solutions over the chart. -/
  equiv (U : SmallEtale B S hS) (k : U ⟶ openObj B S hS T) :
    (U ⟶ obj) ≃
      {a : Fin n → ↥Γ((SmallEtale.toScheme B S hS).obj U, ⊤) //
        MvPolynomial.IsSolution P (relCoeff B S hS T ψ k) a}
  /-- The identification is natural in the chart. -/
  equiv_naturality {U U' : SmallEtale B S hS} (j : U' ⟶ U) (k : U ⟶ openObj B S hS T)
    (f : U ⟶ obj) (i : Fin n) :
    (equiv U' (j ≫ k) (j ≫ f)).1 i = smallEtaleRestrict B S hS j ((equiv U k f).1 i)

namespace RelSolutionPresentation

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T : S.Opens}
  {R : Type u} [CommRing R] {ψ : R →+* ↥Γ((SmallEtale.toScheme B S hS).obj (openObj B S hS T), ⊤)}
  {n : ℕ} {P : Fin n → MvPolynomial (Fin n) R} (pres : RelSolutionPresentation B S hS T ψ P)

/-- The coordinates do not depend on the (unique) morphism to `T`. -/
theorem equiv_congr (U : SmallEtale B S hS) (k k' : U ⟶ openObj B S hS T) (f : U ⟶ pres.obj) :
    (pres.equiv U k f).1 = (pres.equiv U k' f).1 := by
  obtain rfl := Subsingleton.elim k k'
  rfl

/-- The representable sheaf `h_W` of the presented object. -/
abbrev sheaf : Sheaf (SmallEtale.topology B S hS) (Type u) :=
  (smallEtaleYoneda B S hS).obj (RelSolutionPresentation.obj pres)

/-- The `i`-th coordinate of a chart-valued point of `W`. -/
def coord (i : Fin n) : pres.sheaf ⟶ setStructureSheaf B S hS where
  hom :=
    { app := fun U => TypeCat.ofHom fun f => (pres.equiv U.unop (f ≫ pres.over) f).1 i
      naturality := fun U U' j => TypeCat.homEquiv.injective (funext fun f => by
        change (pres.equiv U'.unop ((j.unop ≫ f) ≫ pres.over) (j.unop ≫ f)).1 i =
          smallEtaleRestrict B S hS j.unop ((pres.equiv U.unop (f ≫ pres.over) f).1 i)
        rw [pres.equiv_congr _ _ (j.unop ≫ f ≫ pres.over)]
        exact pres.equiv_naturality j.unop _ f i) }

/-- The `i`-th coordinate of a chart-valued point `f` is the `i`-th entry of the solution `f`
corresponds to, read through the morphism to `T` that `f` itself determines. -/
@[simp]
theorem coord_hom_app (i : Fin n) (U : (SmallEtale B S hS)ᵒᵖ) (f : U.unop ⟶ pres.obj) :
    (pres.coord i).hom.app U f = (pres.equiv U.unop (f ≫ pres.over) f).1 i :=
  rfl

/-- The coordinates of a chart-valued point may be read through any morphism from the chart
to `T`, since there is at most one. -/
theorem coord_hom_app' (i : Fin n) (U : (SmallEtale B S hS)ᵒᵖ) (f : U.unop ⟶ pres.obj)
    (k : U.unop ⟶ openObj B S hS T) :
    (pres.coord i).hom.app U f = (pres.equiv U.unop k f).1 i :=
  congrFun (pres.equiv_congr _ _ _ f) i

/-- Two morphisms of sheaves of sets which agree on all sections are equal. -/
private theorem sheaf_hom_ext_of_apply {G G' : Sheaf (SmallEtale.topology B S hS) (Type u)}
    {a b : G ⟶ G'} (h : ∀ (U : (SmallEtale B S hS)ᵒᵖ) (t : G.obj.obj U),
      a.hom.app U t = b.hom.app U t) :
    a = b :=
  Sheaf.hom_ext (NatTrans.ext (funext fun U => TypeCat.homEquiv.injective (funext (h U))))

/-- Two morphisms of sheaves into `h_W` which agree on all coordinates are equal. -/
theorem hom_ext {G : Sheaf (SmallEtale.topology B S hS) (Type u)} (a b : G ⟶ pres.sheaf)
    (h : ∀ i, a ≫ pres.coord i = b ≫ pres.coord i) :
    a = b := by
  refine sheaf_hom_ext_of_apply fun U t => ?_
  let k : U.unop ⟶ openObj B S hS T := a.hom.app U t ≫ pres.over
  refine (pres.equiv U.unop k).injective (Subtype.ext (funext fun i => ?_))
  have hi := congrArg (fun α : G ⟶ setStructureSheaf B S hS => α.hom.app U t) (h i)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, types_comp_apply] at hi
  exact (pres.coord_hom_app' i U (a.hom.app U t) k).symm.trans
    (hi.trans (pres.coord_hom_app' i U (b.hom.app U t) k))

/-- **The universal property of `h_W` among sheaves lying over `T`.**  A sheaf of sets `F` with
a morphism `π : F ⟶ h_T` and `n` morphisms `sᵢ : F ⟶ 𝒪_S` whose values over every chart solve
the system (with the coefficients of that chart) admits exactly one morphism `F ⟶ h_W` with
coordinates `sᵢ`. -/
theorem existsUnique_hom (F : Sheaf (SmallEtale.topology B S hS) (Type u))
    (π : F ⟶ openSheaf B S hS T) (s : Fin n → (F ⟶ setStructureSheaf B S hS))
    (hs : ∀ (U : (SmallEtale B S hS)ᵒᵖ) (t : F.obj.obj U),
      MvPolynomial.IsSolution P (relCoeff B S hS T ψ (π.hom.app U t))
        (fun i => (s i).hom.app U t)) :
    ∃! φ : F ⟶ pres.sheaf, ∀ i, φ ≫ pres.coord i = s i := by
  let a : ∀ U : (SmallEtale B S hS)ᵒᵖ, F.obj.obj U → (U.unop ⟶ pres.obj) :=
    fun U t => (pres.equiv U.unop (π.hom.app U t)).symm ⟨fun i => (s i).hom.app U t, hs U t⟩
  have hcoord : ∀ (U : (SmallEtale B S hS)ᵒᵖ) (t : F.obj.obj U) (i : Fin n),
      (pres.equiv U.unop (π.hom.app U t) (a U t)).1 i = (s i).hom.app U t :=
    fun U t i => congrFun (congrArg Subtype.val
      ((pres.equiv U.unop (π.hom.app U t)).apply_symm_apply ⟨fun j => (s j).hom.app U t, hs U t⟩)) i
  have hπ : ∀ (U U' : (SmallEtale B S hS)ᵒᵖ) (k : U ⟶ U') (t : F.obj.obj U),
      π.hom.app U' (F.obj.map k t) = k.unop ≫ π.hom.app U t := fun _ _ _ _ => Subsingleton.elim _ _
  have hnat : ∀ (U U' : (SmallEtale B S hS)ᵒᵖ) (k : U ⟶ U') (t : F.obj.obj U),
      a U' (F.obj.map k t) = k.unop ≫ a U t := by
    intro U U' k t
    refine (pres.equiv U'.unop (π.hom.app U' (F.obj.map k t))).injective
      (Subtype.ext (funext fun i => ?_))
    refine (hcoord U' (F.obj.map k t) i).trans ?_
    refine (ConcreteCategory.congr_hom ((s i).hom.naturality k) t).trans ?_
    exact (congrArg (smallEtaleRestrict B S hS k.unop) (hcoord U t i)).symm.trans
      ((pres.equiv_naturality k.unop _ (a U t) i).symm.trans
        (congrFun (pres.equiv_congr _ _ _ _) i))
  refine ⟨⟨{ app := fun U => TypeCat.ofHom (a U)
             naturality := fun U U' k =>
               TypeCat.homEquiv.injective (funext fun t => hnat U U' k t) }⟩, fun i => ?_, ?_⟩
  · refine sheaf_hom_ext_of_apply fun U t => ?_
    exact (pres.coord_hom_app' i U (a U t) (π.hom.app U t)).trans (hcoord U t i)
  · intro χ hχ
    refine sheaf_hom_ext_of_apply fun U t => ?_
    refine Eq.trans ((pres.equiv U.unop (π.hom.app U t)).symm_apply_apply (χ.hom.app U t)).symm ?_
    refine congrArg (pres.equiv U.unop (π.hom.app U t)).symm (Subtype.ext (funext fun i => ?_))
    refine (pres.coord_hom_app' i U _ _).symm.trans ?_
    exact congrArg (fun α : F ⟶ setStructureSheaf B S hS => α.hom.app U t) (hχ i)

/-- The morphism `F ⟶ h_W` of `AlgebraicGeometry.RelSolutionPresentation.existsUnique_hom`. -/
def homOfIsSolution (F : Sheaf (SmallEtale.topology B S hS) (Type u))
    (π : F ⟶ openSheaf B S hS T) (s : Fin n → (F ⟶ setStructureSheaf B S hS))
    (hs : ∀ (U : (SmallEtale B S hS)ᵒᵖ) (t : F.obj.obj U),
      MvPolynomial.IsSolution P (relCoeff B S hS T ψ (π.hom.app U t))
        (fun i => (s i).hom.app U t)) :
    F ⟶ pres.sheaf :=
  (pres.existsUnique_hom F π s hs).choose

/-- The coordinates of `AlgebraicGeometry.RelSolutionPresentation.homOfIsSolution` are the
morphisms `sᵢ` it was built from. -/
theorem homOfIsSolution_comp_coord (F : Sheaf (SmallEtale.topology B S hS) (Type u))
    (π : F ⟶ openSheaf B S hS T) (s : Fin n → (F ⟶ setStructureSheaf B S hS))
    (hs : ∀ (U : (SmallEtale B S hS)ᵒᵖ) (t : F.obj.obj U),
      MvPolynomial.IsSolution P (relCoeff B S hS T ψ (π.hom.app U t))
        (fun i => (s i).hom.app U t)) (i : Fin n) :
    pres.homOfIsSolution F π s hs ≫ pres.coord i = s i :=
  (pres.existsUnique_hom F π s hs).choose_spec.1 i

/-- The morphism `h_W ⟶ h_T`. -/
abbrev toOpenSheaf : pres.sheaf ⟶ openSheaf B S hS T := (smallEtaleYoneda B S hS).map pres.over

end RelSolutionPresentation

/-! ### The stalk of a relative solution sheaf -/

section StalkCoeff

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T : S.Opens)
  {R : Type u} [CommRing R] (ψ : R →+* ↥Γ((SmallEtale.toScheme B S hS).obj (openObj B S hS T), ⊤))
  (p : (SmallEtale.topology B S hS).Point.{u})

/-- **The coefficients at a point do not depend on the chart over `T` they are read on.** -/
theorem smallEtaleGermHom_comp_relCoeff_eq {U U' : SmallEtale B S hS} (x : p.fiber.obj U)
    (x' : p.fiber.obj U') (k : U ⟶ openObj B S hS T) (k' : U' ⟶ openObj B S hS T) :
    (smallEtaleGermHom B S hS p U x).comp (relCoeff B S hS T ψ k) =
      (smallEtaleGermHom B S hS p U' x').comp (relCoeff B S hS T ψ k') := by
  obtain ⟨W, z, g, g', hg, hg'⟩ := Stacks.exists_common_neighbourhood p x x'
  have main : ∀ (V : SmallEtale B S hS) (y : p.fiber.obj V) (kV : V ⟶ openObj B S hS T)
      (j : W ⟶ V), p.fiber.map j z = y →
      (smallEtaleGermHom B S hS p V y).comp (relCoeff B S hS T ψ kV) =
        (smallEtaleGermHom B S hS p W z).comp (relCoeff B S hS T ψ (g ≫ k)) := by
    intro V y kV j hj
    rw [Subsingleton.elim (g ≫ k) (j ≫ kV), ← relCoeff_comp, ← RingHom.comp_assoc, ← hj,
      smallEtaleGermHom_comp_restrict B S hS p j z]
  rw [main U x k g hg, main U' x' k' g' hg']

/-- Germs at a point are compatible with restriction, as functions on sections. -/
private theorem smallEtaleGermHom_restrict_apply {U U' : SmallEtale B S hS} (k : U' ⟶ U)
    (x : p.fiber.obj U') (y : p.fiber.obj U) (hxy : p.fiber.map k x = y)
    (a : ↥Γ((SmallEtale.toScheme B S hS).obj U, ⊤)) :
    smallEtaleGermHom B S hS p U' x (smallEtaleRestrict B S hS k a) =
      smallEtaleGermHom B S hS p U y a :=
  hxy ▸ RingHom.congr_fun (smallEtaleGermHom_comp_restrict B S hS p k x) a

/-- The solutions of the system in the stalk ring at `p`, with the coefficients read on a chart
`U₀` over `T` through which `p` passes. -/
abbrev relStalkSolutionSet {U₀ : SmallEtale B S hS} (x₀ : p.fiber.obj U₀)
    (k₀ : U₀ ⟶ openObj B S hS T) {n : ℕ} (P : Fin n → MvPolynomial (Fin n) R) : Type u :=
  {α : Fin n → ↥(smallEtaleStalkRing B S hS p) //
    MvPolynomial.IsSolution P ((smallEtaleGermHom B S hS p U₀ x₀).comp (relCoeff B S hS T ψ k₀)) α}

end StalkCoeff

namespace RelSolutionPresentation

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T : S.Opens}
  {R : Type u} [CommRing R] {ψ : R →+* ↥Γ((SmallEtale.toScheme B S hS).obj (openObj B S hS T), ⊤)}
  {n : ℕ} {P : Fin n → MvPolynomial (Fin n) R} (pres : RelSolutionPresentation B S hS T ψ P)
  (p : (SmallEtale.topology B S hS).Point.{u}) {U₀ : SmallEtale B S hS} (x₀ : p.fiber.obj U₀)
  (k₀ : U₀ ⟶ openObj B S hS T)

/-- The coordinates of a chart-valued point of `W`, read as germs, solve the system in the stalk
ring. -/
theorem isSolution_germ_equiv (U : SmallEtale B S hS) (x : p.fiber.obj U) (f : U ⟶ pres.obj) :
    MvPolynomial.IsSolution P
      ((smallEtaleGermHom B S hS p U₀ x₀).comp (relCoeff B S hS T ψ k₀))
      (fun i => smallEtaleGermHom B S hS p U x ((pres.equiv U (f ≫ pres.over) f).1 i)) :=
  (smallEtaleGermHom_comp_relCoeff_eq B S hS T ψ p x x₀ (f ≫ pres.over) k₀) ▸
    MvPolynomial.isSolution_comp _ (smallEtaleGermHom B S hS p U x)
      (pres.equiv U (f ≫ pres.over) f).2

/-- The germs of the coordinates of a chart-valued point of `W`, as a solution in the stalk. -/
def stalkSolutionFamily (U : SmallEtale B S hS) (x : p.fiber.obj U) :
    pres.sheaf.obj.obj (op U) ⟶ relStalkSolutionSet B S hS T ψ p x₀ k₀ P :=
  TypeCat.ofHom fun f => ⟨fun i => smallEtaleGermHom B S hS p U x
      ((pres.equiv U (f ≫ pres.over) f).1 i), pres.isSolution_germ_equiv p x₀ k₀ U x f⟩

/-- The families of germs are compatible with the transition maps of the point, which is what
lets them be assembled into a map out of the stalk. -/
theorem stalkSolutionFamily_compat ⦃U U' : SmallEtale B S hS⦄ (k : U ⟶ U')
    (x : p.fiber.obj U) :
    pres.sheaf.obj.map k.op ≫ pres.stalkSolutionFamily p x₀ k₀ U x =
      pres.stalkSolutionFamily p x₀ k₀ U' (p.fiber.map k x) := by
  refine TypeCat.homEquiv.injective (funext fun f => Subtype.ext (funext fun i => ?_))
  show smallEtaleGermHom B S hS p U x ((pres.equiv U ((k ≫ f) ≫ pres.over) (k ≫ f)).1 i) =
    smallEtaleGermHom B S hS p U' (p.fiber.map k x) ((pres.equiv U' (f ≫ pres.over) f).1 i)
  rw [pres.equiv_congr _ _ (k ≫ f ≫ pres.over), pres.equiv_naturality k _ f i,
    ← smallEtaleGermHom_comp_restrict B S hS p k x]
  rfl

/-- **The stalk of `h_W` at `p` maps to the solutions in the stalk ring.** -/
def stalkSolutionHom :
    (p.presheafFiber (A := Type u)).obj pres.sheaf.obj ⟶ relStalkSolutionSet B S hS T ψ p x₀ k₀ P :=
  p.presheafFiberDesc (pres.stalkSolutionFamily p x₀ k₀) (pres.stalkSolutionFamily_compat p x₀ k₀)

/-- The underlying map of `AlgebraicGeometry.RelSolutionPresentation.stalkSolutionHom`. -/
abbrev stalkSolution :
    ToType ((p.presheafFiber (A := Type u)).obj pres.sheaf.obj) →
      relStalkSolutionSet B S hS T ψ p x₀ k₀ P :=
  ConcreteCategory.hom (pres.stalkSolutionHom p x₀ k₀)

/-- The solution attached to the class of a chart-valued point `f` is the family of germs of the
coordinates of `f`. -/
theorem stalkSolution_toPresheafFiber_coe (U : SmallEtale B S hS) (x : p.fiber.obj U)
    (f : U ⟶ pres.obj) (i : Fin n) :
    (pres.stalkSolution p x₀ k₀ (p.toPresheafFiber U x pres.sheaf.obj f)).1 i =
      smallEtaleGermHom B S hS p U x ((pres.equiv U (f ≫ pres.over) f).1 i) := by
  have h := ConcreteCategory.congr_hom (p.toPresheafFiber_presheafFiberDesc
    (pres.stalkSolutionFamily p x₀ k₀) (pres.stalkSolutionFamily_compat p x₀ k₀) U x) f
  exact congrFun (congrArg Subtype.val h) i

/-- A class in the stalk of `h_W` is determined by the germs of its coordinates: two chart-valued
points with the same germs agree after restricting to a smaller chart. -/
theorem injective_stalkSolution : Function.Injective (pres.stalkSolution p x₀ k₀) := by
  intro t₁ t₂ h
  obtain ⟨U, x, e₁, e₂, rfl, rfl⟩ :=
    p.toPresheafFiber_jointly_surjective₂ (P := pres.sheaf.obj) t₁ t₂
  let f₁ : U ⟶ pres.obj := e₁
  let f₂ : U ⟶ pres.obj := e₂
  let kU : U ⟶ openObj B S hS T := f₁ ≫ pres.over
  have hco : ∀ i, smallEtaleGermHom B S hS p U x ((pres.equiv U kU f₁).1 i) =
      smallEtaleGermHom B S hS p U x ((pres.equiv U kU f₂).1 i) := by
    intro i
    rw [← pres.coord_hom_app' i (op U) f₁ kU, ← pres.coord_hom_app' i (op U) f₂ kU,
      pres.coord_hom_app, pres.coord_hom_app,
      ← pres.stalkSolution_toPresheafFiber_coe p x₀ k₀ U x f₁ i,
      ← pres.stalkSolution_toPresheafFiber_coe p x₀ k₀ U x f₂ i]
    exact congrFun (congrArg Subtype.val h) i
  obtain ⟨W, k, z, hz, hk⟩ :=
    exists_restrict_eq_of_forall_germ_eq p (SmallEtale.commRingStructureSheaf B S hS).obj n U x
      (fun i => (pres.equiv U kU f₁).1 i) (fun i => (pres.equiv U kU f₂).1 i) hco
  have hcomp : k ≫ f₁ = k ≫ f₂ :=
    (pres.equiv W (k ≫ kU)).injective (Subtype.ext (funext fun i => by
      rw [pres.equiv_naturality k kU f₁ i, pres.equiv_naturality k kU f₂ i]
      exact hk i))
  have hmap : pres.sheaf.obj.map k.op e₁ = pres.sheaf.obj.map k.op e₂ := hcomp
  rw [← hz, ← p.toPresheafFiber_w_apply k z pres.sheaf.obj,
    ← p.toPresheafFiber_w_apply k z pres.sheaf.obj, hmap]

/-- Every solution in the stalk ring comes from a class in the stalk of `h_W`: lift the
coordinates to a chart through which `p` passes, shrink it so that the polynomials vanish on the
nose, and take the chart-valued point the resulting solution corresponds to. -/
theorem surjective_stalkSolution : Function.Surjective (pres.stalkSolution p x₀ k₀) := by
  rintro ⟨α, hα⟩
  obtain ⟨U₁, x₁, z₁, hz₁⟩ :=
    Stacks.exists_toPresheafFiber_fin p (P := (SmallEtale.commRingStructureSheaf B S hS).obj) α
  obtain ⟨U, x, g₁, g₀, hg₁, hg₀⟩ := Stacks.exists_common_neighbourhood p x₁ x₀
  let kU : U ⟶ openObj B S hS T := g₀ ≫ k₀
  let z : Fin n → ↥Γ((SmallEtale.toScheme B S hS).obj U, ⊤) :=
    fun i => smallEtaleRestrict B S hS g₁ (z₁ i)
  have hzg : ∀ i, smallEtaleGermHom B S hS p U x (z i) = α i := by
    exact fun i => (smallEtaleGermHom_restrict_apply B S hS p g₁ x x₁ hg₁ (z₁ i)).trans (hz₁ i)
  have hcoef : (smallEtaleGermHom B S hS p U x).comp (relCoeff B S hS T ψ kU) =
      (smallEtaleGermHom B S hS p U₀ x₀).comp (relCoeff B S hS T ψ k₀) :=
    smallEtaleGermHom_comp_relCoeff_eq B S hS T ψ p x x₀ kU k₀
  have hvanish : ∀ j, smallEtaleGermHom B S hS p U x
      (MvPolynomial.eval z (MvPolynomial.map (relCoeff B S hS T ψ kU) (P j))) = 0 := by
    intro j
    rw [← MvPolynomial.eval_map_ringHom_comp (relCoeff B S hS T ψ kU)
      (smallEtaleGermHom B S hS p U x) z (P j), hcoef,
      show (fun i => smallEtaleGermHom B S hS p U x (z i)) = α from funext hzg]
    exact hα j
  obtain ⟨W, k, y, hy, hk⟩ :=
    exists_restrict_eq_zero_of_forall_germ_eq_zero p
      (SmallEtale.commRingStructureSheaf B S hS).obj U x
      (fun j => MvPolynomial.eval z (MvPolynomial.map (relCoeff B S hS T ψ kU) (P j)))
      hvanish
  have hsol : MvPolynomial.IsSolution P (relCoeff B S hS T ψ (k ≫ kU))
      (fun i => smallEtaleRestrict B S hS k (z i)) := by
    intro j
    rw [← relCoeff_comp, MvPolynomial.eval_map_ringHom_comp (relCoeff B S hS T ψ kU)
        (smallEtaleRestrict B S hS k) z (P j)]
    exact hk j
  refine ⟨p.toPresheafFiber W y pres.sheaf.obj ((pres.equiv W (k ≫ kU)).symm ⟨_, hsol⟩), ?_⟩
  refine Subtype.ext (funext fun i => ?_)
  rw [pres.stalkSolution_toPresheafFiber_coe p x₀ k₀ W y _ i,
    pres.equiv_congr _ _ (k ≫ kU), (pres.equiv W (k ≫ kU)).apply_symm_apply]
  exact (smallEtaleGermHom_restrict_apply B S hS p k y _ hy (z i)).trans (hzg i)

/-- **The stalk of a relative solution sheaf at a point over `T` is the solution set of the
stalk.** -/
theorem bijective_stalkSolution : Function.Bijective (pres.stalkSolution p x₀ k₀) :=
  ⟨pres.injective_stalkSolution p x₀ k₀, pres.surjective_stalkSolution p x₀ k₀⟩

end RelSolutionPresentation

end AlgebraicGeometry

end
