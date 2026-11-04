module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomRepresentable
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeIsom

/-!
# The Isom functor as the mutually inverse pairs of homomorphisms

The proof of Stacks 08K9 identifies the relative Isom functor of Stacks 08K7 with a fibre
product of relative Hom functors.  Writing `H = Hom(F, G)`, `H' = Hom(G, F)`,
`I = Hom(F, F)` and `I' = Hom(G, G)`, the composition of homomorphisms is a morphism

`c : H' ×_B H ⟶ I ×_B I'`, `(u', u) ↦ (u ∘ u', u' ∘ u)`

over the base, the pair of identity homomorphisms is a section `σ : B ⟶ I ×_B I'`, and

`Isom(F, G) = (H' ×_B H) ×_{c, I ×_B I', σ} B`.

This file proves that identification, with no hypothesis, as an isomorphism of functors on the
test schemes over the base.  Since every functor here is indexed by the test schemes over the
base, the fibre products over `B` are pointwise products of functors, and the fibre product
over `I ×_B I'` along `σ` is cut out by the two equations `u ∘ u' = id` and `u' ∘ u = id`.

## Main definitions

* `AlgebraicGeometry.Space.HomSituation.swap`,
  `AlgebraicGeometry.Space.HomSituation.endoSource` and
  `AlgebraicGeometry.Space.HomSituation.endoTarget`: the situations of Stacks 08JT whose
  relative Hom functors are `H' = Hom(G, F)`, `I = Hom(F, F)` and `I' = Hom(G, G)`.
* `AlgebraicGeometry.Space.HomSituation.mutualInverseFunctor`: the fibre product
  `(H' ×_B H) ×_{c, I ×_B I', σ} B`, as a functor on the test schemes over the base: the pairs
  `(u', u)` of homomorphisms `G_T ⟶ F_T` and `F_T ⟶ G_T` whose two composites are the two
  identity homomorphisms.
* `AlgebraicGeometry.Space.HomSituation.mutualInverseFunctorIsoIsom` and
  `AlgebraicGeometry.Space.HomSituation.isomFunctorIsoMutualInverse`: the isomorphism
  `Isom(F, G) ≅ (H' ×_B H) ×_{c, I ×_B I', σ} B` of functors on the test schemes over the base.

## Main results

* `CategoryTheory.Functor.conjHom_id_morphism` and
  `CategoryTheory.Functor.conjHom_comp_morphism`: conjugation by a comparison of a functor
  with a composite carries identities to identities and composites to composites.

## Implementation notes

The three auxiliary situations are `{s with ...}` updates, so they share `X`, `base` and `f`
with the given situation definitionally; the comparison of base changes
`AlgebraicGeometry.Space.HomSituation.baseChangeComparison` depends only on `f`, so a single
comparison conjugates homomorphisms of all four pairs of modules.

## References

* [Stacks Project, Tag 08K9](https://stacks.math.columbia.edu/tag/08K9)
* [Stacks Project, Tag 08K7](https://stacks.math.columbia.edu/tag/08K7)
* [Stacks Project, Tag 08JT](https://stacks.math.columbia.edu/tag/08JT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C : Type*} [Category* C] {D₁ : Type*} [Category* D₁] {D₂ : Type*} [Category* D₂]

/-- Conjugating the identity of `P₁.obj M` by a comparison `P₂ ≅ P₁ ⋙ L` gives the identity of
`P₂.obj M`. -/
theorem conjHom_id_morphism {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} (e : P₂ ≅ P₁ ⋙ L)
    (M : C) : conjHom e (𝟙 (P₁.obj M)) = 𝟙 (P₂.obj M) := by
  simp [conjHom]

/-- Conjugating a composite of two morphisms between values of `P₁` by a comparison
`P₂ ≅ P₁ ⋙ L` gives the composite of the two conjugates. -/
theorem conjHom_comp_morphism {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} (e : P₂ ≅ P₁ ⋙ L)
    {M N K : C} (α : P₁.obj M ⟶ P₁.obj N) (β : P₁.obj N ⟶ P₁.obj K) :
    conjHom e (α ≫ β) = conjHom e α ≫ conjHom e β := by
  simp [conjHom]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space.HomSituation

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (s : HomSituation B S hS)

/-- The situation of Stacks 08JT with the two modules exchanged: its relative Hom functor is
`H' = Hom(G, F)`. -/
def swap : HomSituation B S hS :=
  { s with
    F := s.G
    G := s.F
    quasicoherent_F := s.quasicoherent_G
    quasicoherent_G := s.quasicoherent_F }

/-- The situation of Stacks 08JT with both modules the source module: its relative Hom
functor is `I = Hom(F, F)`. -/
def endoSource : HomSituation B S hS :=
  { s with G := s.F, quasicoherent_G := s.quasicoherent_F }

/-- The situation of Stacks 08JT with both modules the target module: its relative Hom
functor is `I' = Hom(G, G)`. -/
def endoTarget : HomSituation B S hS :=
  { s with F := s.G, quasicoherent_F := s.quasicoherent_G }

/-- The situation `swap` has the same morphism `f` as `s`. -/
@[simp] theorem swap_f : s.swap.f = s.f := rfl
/-- The situation `swap` has the same base as `s`. -/
@[simp] theorem swap_base : s.swap.base = s.base := rfl
/-- The situation `endoSource` has the same morphism `f` as `s`. -/
@[simp] theorem endoSource_f : s.endoSource.f = s.f := rfl
/-- The situation `endoTarget` has the same morphism `f` as `s`. -/
@[simp] theorem endoTarget_f : s.endoTarget.f = s.f := rfl

/-- A homomorphism of base-changed modules, read as the section of the relative Hom functor
that it is: the inverse of `AlgebraicGeometry.Space.HomSituation.toModuleHom`. -/
def ofModuleHom {T : s.SchemesOver}
    (α : s.baseChangedModule T s.F ⟶ s.baseChangedModule T s.G) : s.homAt T :=
  α

/-- Reading a section built by `ofModuleHom` back as a module homomorphism recovers it. -/
@[simp] theorem toModuleHom_ofModuleHom {T : s.SchemesOver}
    (α : s.baseChangedModule T s.F ⟶ s.baseChangedModule T s.G) :
    s.toModuleHom (s.ofModuleHom α) = α :=
  rfl

/-- A section of the relative Hom functor is `ofModuleHom` of its module homomorphism. -/
@[simp] theorem ofModuleHom_toModuleHom {T : s.SchemesOver} (α : s.homAt T) :
    s.ofModuleHom (s.toModuleHom α) = α :=
  rfl

/-- The pairs of mutually inverse homomorphisms at a test scheme `T` over the base: pairs
`(u', u)` with `u : F_T ⟶ G_T` and `u' : G_T ⟶ F_T` whose two composites are the identity
homomorphisms of `F_T` and of `G_T`. -/
abbrev MutualInverseAt (T : s.SchemesOver) : Type (u + 1) :=
  {q : (s.baseChangedModule T s.G ⟶ s.baseChangedModule T s.F) ×
      (s.baseChangedModule T s.F ⟶ s.baseChangedModule T s.G) //
    q.2 ≫ q.1 = 𝟙 (s.baseChangedModule T s.F) ∧
      q.1 ≫ q.2 = 𝟙 (s.baseChangedModule T s.G)}

/-- Pullback of a mutually inverse pair along a morphism of test schemes: each coordinate is
conjugated by the comparison of the two base changes. -/
def mutualInverseMap {U T : s.SchemesOver} (g : U ⟶ T) (q : s.MutualInverseAt T) :
    s.MutualInverseAt U :=
  ⟨(Functor.conjHom (s.baseChangeComparison g) q.1.1,
      Functor.conjHom (s.baseChangeComparison g) q.1.2),
    by rw [← Functor.conjHom_comp_morphism, q.2.1, Functor.conjHom_id_morphism],
    by rw [← Functor.conjHom_comp_morphism, q.2.2, Functor.conjHom_id_morphism]⟩

/-- Pullback of mutually inverse pairs along the identity is the identity. -/
theorem mutualInverseMap_id (T : s.SchemesOver) (q : s.MutualInverseAt T) :
    s.mutualInverseMap (𝟙 T) q = q := by
  refine Subtype.ext (Prod.ext ?_ ?_) <;>
    exact Functor.conjHom_id _ _
      (s.baseChangeComparison_id (modulePushforwardCoherence B S hS) T) _

/-- Pullback of mutually inverse pairs along a composite is the composite of the
pullbacks. -/
theorem mutualInverseMap_comp {V U T : s.SchemesOver} (g : V ⟶ U) (h : U ⟶ T)
    (q : s.MutualInverseAt T) :
    s.mutualInverseMap (g ≫ h) q = s.mutualInverseMap g (s.mutualInverseMap h q) := by
  refine Subtype.ext (Prod.ext ?_ ?_) <;>
    exact Functor.conjHom_comp (s.baseChangeComparison h) (s.baseChangeComparison g)
      (s.baseChangeComparison (g ≫ h))
      (modulePullbackTriangle B S hS (baseChangeMap_comp s.f g h).symm)
      (s.baseChangeComparison_comp (modulePushforwardCoherence B S hS) g h) _

/-- The mutually inverse pairs of homomorphisms, as a functor on the test schemes over the base:
the fibre product `(H' ×_B H) ×_{c, I ×_B I', σ} B`. -/
@[sga "6 XII 2.4" "Functor of points of Z"]
def mutualInverseFunctor : (s.SchemesOver)ᵒᵖ ⥤ Type (u + 1) where
  obj V := s.MutualInverseAt V.unop
  map i := ↾s.mutualInverseMap i.unop
  map_id V := ConcreteCategory.hom_ext _ _ (s.mutualInverseMap_id V.unop)
  map_comp i j :=
    ConcreteCategory.hom_ext _ _ fun q ↦ s.mutualInverseMap_comp j.unop i.unop q

/-- The section of the relative Isom functor given by the second coordinate of a mutually
inverse pair. -/
def isomOfMutualInverse {V : (s.SchemesOver)ᵒᵖ} (q : s.mutualInverseFunctor.obj V) :
    s.isomFunctor.obj V :=
  ⟨s.ofModuleHom q.1.2, ⟨⟨q.1.1, q.2.1, q.2.2⟩⟩⟩

/-- The mutually inverse pair formed by the inverse of a section of the relative Isom functor
and the section itself. -/
def mutualInverseOfIsom {V : (s.SchemesOver)ᵒᵖ} (α : s.isomFunctor.obj V) :
    s.mutualInverseFunctor.obj V :=
  haveI : IsIso (s.toModuleHom α.1) := α.2
  ⟨(inv (s.toModuleHom α.1), s.toModuleHom α.1), IsIso.hom_inv_id _, IsIso.inv_hom_id _⟩

/-- At each test scheme over the base, the invertible homomorphisms `F_T ⟶ G_T`, the sections
of the relative Isom functor, correspond to the pairs `(u', u)` whose two composites are the
identity homomorphisms: a pair goes to its second coordinate, and an invertible homomorphism
goes to the pair consisting of its inverse and itself. -/
def mutualInverseEquivIsom (V : (s.SchemesOver)ᵒᵖ) :
    s.mutualInverseFunctor.obj V ≃ s.isomFunctor.obj V where
  toFun := s.isomOfMutualInverse
  invFun := s.mutualInverseOfIsom
  left_inv q := by
    have : IsIso (s.toModuleHom (s.isomOfMutualInverse q).1) :=
      (s.isomOfMutualInverse q).2
    exact Subtype.ext (Prod.ext (IsIso.inv_eq_of_hom_inv_id q.2.1) rfl)
  right_inv _ := rfl

/-- The homomorphism of base-changed modules underlying the image of an invertible section
under a morphism of test schemes is the conjugate, by the comparison of the two base changes, of
the homomorphism underlying the section. -/
theorem toModuleHom_isomFunctor_map {V W : (s.SchemesOver)ᵒᵖ} (i : V ⟶ W)
    (α : s.isomFunctor.obj V) :
    s.toModuleHom ((s.isomFunctor.map i) α).1 =
      Functor.conjHom (s.baseChangeComparison i.unop) (s.toModuleHom α.1) := by
  have e : (s.homFunctor (modulePushforwardCoherence B S hS)).map i =
      TypeCat.ofHom (s.homMap i.unop) := by
    rw [← Quiver.Hom.op_unop i]
    exact s.homFunctor_map (modulePushforwardCoherence B S hS) i.unop
  have h : ((s.homFunctor (modulePushforwardCoherence B S hS)).map i) α.1 =
      s.homMap i.unop α.1 := by
    rw [e]
    rfl
  exact (congrArg s.toModuleHom h).trans (s.toModuleHom_homMap i.unop α.1)

/-- A section of the relative Hom functor is determined by the homomorphism of base-changed
modules that it is. -/
theorem toModuleHom_injective {T : s.SchemesOver} {α β : s.homAt T}
    (h : s.toModuleHom α = s.toModuleHom β) : α = β :=
  h

/-- The homomorphism of base-changed modules underlying the section of the relative Isom
functor attached to a mutually inverse pair is the pair's second coordinate. -/
theorem toModuleHom_isomOfMutualInverse {V : (s.SchemesOver)ᵒᵖ}
    (q : s.mutualInverseFunctor.obj V) :
    s.toModuleHom (s.isomOfMutualInverse q).1 = q.1.2 :=
  rfl

/-- A morphism of test schemes acts on the mutually inverse pairs by pullback in each
coordinate. -/
theorem mutualInverseFunctor_map {V W : (s.SchemesOver)ᵒᵖ} (i : V ⟶ W) :
    s.mutualInverseFunctor.map i = ↾s.mutualInverseMap i.unop :=
  rfl

/-- `isomOfMutualInverse` is natural in the test scheme. -/
theorem isomOfMutualInverse_naturality {V W : (s.SchemesOver)ᵒᵖ} (i : V ⟶ W)
    (q : s.mutualInverseFunctor.obj V) :
    s.isomOfMutualInverse (s.mutualInverseFunctor.map i q) =
      (s.isomFunctor.map i) (s.isomOfMutualInverse q) := by
  refine Subtype.ext (s.toModuleHom_injective ?_)
  refine (s.toModuleHom_isomOfMutualInverse _).trans ?_
  rw [s.mutualInverseFunctor_map i]
  exact ((s.toModuleHom_isomFunctor_map i (s.isomOfMutualInverse q)).trans
    (congrArg (fun β ↦ Functor.conjHom (s.baseChangeComparison i.unop) β)
      (s.toModuleHom_isomOfMutualInverse q))).symm

/-- The functor of mutually inverse pairs `(H' ×_B H) ×_{c, I ×_B I', σ} B` is isomorphic to
the relative Isom functor `Isom(F, G)` of Stacks 08K7. -/
@[stacks 08K9 "ONLY the identification Isom(F,G) = (H' x_B H) x_{c, I x_B I', sigma} B that \
the proof rests on, with no hypothesis on f, F or G. The conclusion of Stacks 08K9 — that \
Isom(F,G) is an algebraic space affine of finite presentation over B — is NOT covered. It \
needs, first, the conclusion of Stacks 08K6 for the four Hom functors, which this \
development does not have (Stacks 08K6 in turn needs Stacks 08JY, 08JV, 07V7 and 08K2, of \
which only Stacks 08K2 is proved in this library, as \
AlgebraicGeometry.Space.MorphismDescentSituation.exists_isProperOver_supportOfSheaf_moduleAt); \
and second, stability of \
AlgebraicGeometry.Space.IsAffineHom and of \
AlgebraicGeometry.Space.IsFinitePresentation under base change along a morphism of \
algebraic spaces, which this library does not prove — only isAffineHom_comp and \
isLocallyOfFinitePresentation_of_comp exist — and which the fibre-product step needs. The \
remaining inputs of the source's proof, Stacks 03KP parts (1)-(4) and Stacks 05WT, ARE \
available, in StacksFrontier/AlgebraicGeometry/Spaces/SeparatedCriteria.lean and \
StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/FinitePresentation.lean", sga "6 XII 2.4" "partial"]
def mutualInverseFunctorIsoIsom : s.mutualInverseFunctor ≅ s.isomFunctor :=
  NatIso.ofComponents (fun V ↦ (s.mutualInverseEquivIsom V).toIso)
    (fun i ↦ ConcreteCategory.hom_ext _ _ fun q ↦ s.isomOfMutualInverse_naturality i q)

/-- The relative Isom functor `Isom(F, G)` of Stacks 08K7 is isomorphic to the fibre product
`(H' ×_B H) ×_{c, I ×_B I', σ} B` of the mutually inverse pairs. -/
def isomFunctorIsoMutualInverse : s.isomFunctor ≅ s.mutualInverseFunctor :=
  s.mutualInverseFunctorIsoIsom.symm

end AlgebraicGeometry.Space.HomSituation

end
