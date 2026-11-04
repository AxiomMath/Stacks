module

public import StacksFrontier.AlgebraicGeometry.Quot.AffineFinitePresentationClosure
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeIsomMutualInverse

/-!
# The relative Isom functor is affine and of finite presentation when the Hom functors are

In Situation 08JT write `H = Hom(F, G)`, `H' = Hom(G, F)`, `I = Hom(F, F)` and
`I' = Hom(G, G)`.  The proof of Stacks 08K9 identifies `Isom(F, G)` with the fibre product
`(H' ×_B H) ×_{c, I ×_B I', σ} B`, where `c(u', u) = (u ∘ u', u' ∘ u)` is composition and `σ` is
the pair of identities (`AlgebraicGeometry.Space.HomSituation.isomFunctorIsoMutualInverse`).  So as
soon as the four Hom functors are algebraic spaces affine and of finite presentation over the
base (Stacks 08K6), so is `Isom(F, G)`, by the stability of these under products and under
equations along a section
(`AlgebraicGeometry.Space.IsAffineFinitePresentationAlgebraicSpaceOver.prod`,
`AlgebraicGeometry.Space.IsAffineFinitePresentationAlgebraicSpaceOver.sectionEqualizer`).

## Main definitions

* `AlgebraicGeometry.Space.HomSituation.compositionNatTrans`: the composition
  `c : H' ×_B H ⟶ I ×_B I'`.
* `AlgebraicGeometry.Space.HomSituation.identitySection`: the section `σ` of `I ×_B I'`.

## Main results

* `AlgebraicGeometry.Space.HomSituation.mutualInverseFunctorIsoSectionEqualizer`: the functor of
  mutually inverse pairs is the fibre product of `c` and `σ`.

## References

* [Stacks Project, Tag 08K9](https://stacks.math.columbia.edu/tag/08K9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space.HomSituation

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (s : HomSituation B S hS)
  (hc : ModulePushforwardCoherence B S hS)

/-- The relative Hom functor acts on a section by pullback of homomorphisms. -/
theorem homFunctor_map_apply {V W : (s.SchemesOver)ᵒᵖ} (i : V ⟶ W) (α : s.homAt V.unop) :
    (s.homFunctor hc).map i α = s.homMap i.unop α := by
  have e : (s.homFunctor hc).map i = TypeCat.ofHom (s.homMap i.unop) := by
    rw [← Quiver.Hom.op_unop i]
    exact s.homFunctor_map hc i.unop
  rw [e]
  rfl

/-! ### Reading the sections of the three auxiliary Hom functors as homomorphisms -/

/-- A homomorphism `G_T ⟶ F_T`, read as a section of `H' = Hom(G, F)`. -/
def swapOfModuleHom {T : s.SchemesOver}
    (α : s.baseChangedModule T s.G ⟶ s.baseChangedModule T s.F) : s.swap.homAt T :=
  α

/-- The homomorphism `G_T ⟶ F_T` that a section of `H' = Hom(G, F)` is. -/
def swapToModuleHom {T : s.SchemesOver} (α : s.swap.homAt T) :
    s.baseChangedModule T s.G ⟶ s.baseChangedModule T s.F :=
  α

/-- A homomorphism `F_T ⟶ F_T`, read as a section of `I = Hom(F, F)`. -/
def endoSourceOfModuleHom {T : s.SchemesOver}
    (α : s.baseChangedModule T s.F ⟶ s.baseChangedModule T s.F) : s.endoSource.homAt T :=
  α

/-- A homomorphism `G_T ⟶ G_T`, read as a section of `I' = Hom(G, G)`. -/
def endoTargetOfModuleHom {T : s.SchemesOver}
    (α : s.baseChangedModule T s.G ⟶ s.baseChangedModule T s.G) : s.endoTarget.homAt T :=
  α

/-- Pullback of a section of `H' = Hom(G, F)` is conjugation by the comparison of base changes. -/
theorem swap_homMap {U T : s.SchemesOver} (g : U ⟶ T) (α : s.swap.homAt T) :
    s.swap.homMap g α =
      s.swapOfModuleHom (Functor.conjHom (s.baseChangeComparison g) (s.swapToModuleHom α)) :=
  rfl

/-- Pullback of a section of `I = Hom(F, F)` is conjugation by the comparison of base changes. -/
theorem endoSource_homMap {U T : s.SchemesOver} (g : U ⟶ T)
    (α : s.baseChangedModule T s.F ⟶ s.baseChangedModule T s.F) :
    s.endoSource.homMap g (s.endoSourceOfModuleHom α) =
      s.endoSourceOfModuleHom (Functor.conjHom (s.baseChangeComparison g) α) :=
  rfl

/-- Pullback of a section of `I' = Hom(G, G)` is conjugation by the comparison of base
changes. -/
theorem endoTarget_homMap {U T : s.SchemesOver} (g : U ⟶ T)
    (α : s.baseChangedModule T s.G ⟶ s.baseChangedModule T s.G) :
    s.endoTarget.homMap g (s.endoTargetOfModuleHom α) =
      s.endoTargetOfModuleHom (Functor.conjHom (s.baseChangeComparison g) α) :=
  rfl

/-! ### The composition and the identity section -/

/-- The composition at one test scheme: `(u', u) ↦ (u' ∘ u, u ∘ u')`. -/
def compositionAt (T : s.SchemesOver) (q : s.swap.homAt T × s.homAt T) :
    s.endoSource.homAt T × s.endoTarget.homAt T :=
  (s.endoSourceOfModuleHom (s.toModuleHom q.2 ≫ s.swapToModuleHom q.1),
    s.endoTargetOfModuleHom (s.swapToModuleHom q.1 ≫ s.toModuleHom q.2))

/-- Composition commutes with pullback of homomorphisms. -/
theorem compositionAt_homMap {U T : s.SchemesOver} (g : U ⟶ T)
    (q : s.swap.homAt T × s.homAt T) :
    s.compositionAt U (s.swap.homMap g q.1, s.homMap g q.2) =
      (s.endoSource.homMap g (s.compositionAt T q).1,
        s.endoTarget.homMap g (s.compositionAt T q).2) := by
  refine Prod.ext ?_ ?_
  · show s.endoSourceOfModuleHom (s.toModuleHom (s.homMap g q.2) ≫
        s.swapToModuleHom (s.swap.homMap g q.1)) =
      s.endoSource.homMap g (s.endoSourceOfModuleHom (s.toModuleHom q.2 ≫ s.swapToModuleHom q.1))
    rw [s.endoSource_homMap, s.swap_homMap, s.toModuleHom_homMap]
    exact congrArg s.endoSourceOfModuleHom (Functor.conjHom_comp_morphism _ _ _).symm
  · show s.endoTargetOfModuleHom (s.swapToModuleHom (s.swap.homMap g q.1) ≫
        s.toModuleHom (s.homMap g q.2)) =
      s.endoTarget.homMap g (s.endoTargetOfModuleHom (s.swapToModuleHom q.1 ≫ s.toModuleHom q.2))
    rw [s.endoTarget_homMap, s.swap_homMap, s.toModuleHom_homMap]
    exact congrArg s.endoTargetOfModuleHom (Functor.conjHom_comp_morphism _ _ _).symm

/-- **The composition `c : H' ×_B H ⟶ I ×_B I'`, `(u', u) ↦ (u' ∘ u, u ∘ u')`** of the proof of
Stacks 08K9: a pair of homomorphisms `u' : G_T ⟶ F_T` and `u : F_T ⟶ G_T` goes to its two
composites `F_T ⟶ F_T` and `G_T ⟶ G_T`.  It is natural because pullback of homomorphisms is
conjugation by one comparison of base changes, which carries composites to composites. -/
def compositionNatTrans :
    FunctorToTypes.prod (s.swap.homFunctor hc) (s.homFunctor hc) ⟶
      FunctorToTypes.prod (s.endoSource.homFunctor hc) (s.endoTarget.homFunctor hc) where
  app V := ↾s.compositionAt V.unop
  naturality := fun {V W : (s.SchemesOver)ᵒᵖ} (i : V ⟶ W) =>
    ConcreteCategory.hom_ext _ _ fun (q : s.swap.homAt V.unop × s.homAt V.unop) =>
      (congrArg₂ (fun a b => s.compositionAt W.unop (a, b))
          (s.swap.homFunctor_map_apply hc i q.1) (s.homFunctor_map_apply hc i q.2)).trans
        ((s.compositionAt_homMap i.unop q).trans
          (congrArg₂ Prod.mk (s.endoSource.homFunctor_map_apply hc i _).symm
            (s.endoTarget.homFunctor_map_apply hc i _).symm))

/-- **The section `σ` of `I ×_B I'` given by the two identity homomorphisms.** -/
def identitySection (V : (s.SchemesOver)ᵒᵖ) :
    s.endoSource.homAt V.unop × s.endoTarget.homAt V.unop :=
  (s.endoSourceOfModuleHom (𝟙 _), s.endoTargetOfModuleHom (𝟙 _))

/-- The identity homomorphisms pull back to the identity homomorphisms. -/
theorem identitySection_naturality {V W : (s.SchemesOver)ᵒᵖ} (i : V ⟶ W) :
    (FunctorToTypes.prod (s.endoSource.homFunctor hc) (s.endoTarget.homFunctor hc)).map i
      (s.identitySection V) = s.identitySection W :=
  congrArg₂ Prod.mk
    ((s.endoSource.homFunctor_map_apply hc i _).trans
      ((s.endoSource_homMap i.unop _).trans
        (congrArg s.endoSourceOfModuleHom (Functor.conjHom_id_morphism _ _))))
    ((s.endoTarget.homFunctor_map_apply hc i _).trans
      ((s.endoTarget_homMap i.unop _).trans
        (congrArg s.endoTargetOfModuleHom (Functor.conjHom_id_morphism _ _))))

/-- Pullback of the first coordinate of a mutually inverse pair, read in `H' = Hom(G, F)`. -/
theorem swapOfModuleHom_conjHom {V W : (s.SchemesOver)ᵒᵖ} (i : V ⟶ W)
    (α : s.baseChangedModule V.unop s.G ⟶ s.baseChangedModule V.unop s.F) :
    s.swapOfModuleHom (Functor.conjHom (s.baseChangeComparison i.unop) α) =
      (s.swap.homFunctor hc).map i (s.swapOfModuleHom α) :=
  (s.swap.homFunctor_map_apply hc i _).symm

/-- Pullback of the second coordinate of a mutually inverse pair, read in `H = Hom(F, G)`. -/
theorem conjHom_eq_homFunctor_map {V W : (s.SchemesOver)ᵒᵖ} (i : V ⟶ W)
    (α : s.baseChangedModule V.unop s.F ⟶ s.baseChangedModule V.unop s.G) :
    Functor.conjHom (s.baseChangeComparison i.unop) α = (s.homFunctor hc).map i α :=
  (s.homFunctor_map_apply hc i _).symm

/-- **The functor of mutually inverse pairs is the fibre product of the composition `c` and the
section `σ`**, `(H' ×_B H) ×_{c, I ×_B I', σ} B`. -/
def mutualInverseFunctorIsoSectionEqualizer :
    s.mutualInverseFunctor ≅
      sectionEqualizerFunctor _ _ (s.compositionNatTrans hc) s.identitySection
        (fun i => s.identitySection_naturality hc i) :=
  NatIso.ofComponents
    (fun V => Equiv.toIso
      { toFun := fun q => ⟨(s.swapOfModuleHom q.1.1, q.1.2), congrArg₂ Prod.mk q.2.1 q.2.2⟩
        invFun := fun x => ⟨(s.swapToModuleHom x.1.1, s.toModuleHom x.1.2),
          (Prod.mk.inj x.2).1, (Prod.mk.inj x.2).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })
    (fun {V W} i => by
      refine ConcreteCategory.hom_ext _ _ fun (q : s.MutualInverseAt V.unop) => ?_
      apply Subtype.ext
      change (s.swapOfModuleHom (Functor.conjHom (s.baseChangeComparison i.unop) q.1.1),
          Functor.conjHom (s.baseChangeComparison i.unop) q.1.2) =
        ((s.swap.homFunctor hc).map i (s.swapOfModuleHom q.1.1), (s.homFunctor hc).map i q.1.2)
      exact congrArg₂ Prod.mk (s.swapOfModuleHom_conjHom hc i q.1.1)
        (s.conjHom_eq_homFunctor_map hc i q.1.2))

/-- **Stacks 08K9, the reduction to Stacks 08K6.**  If the four relative Hom functors
`H' = Hom(G, F)`, `H = Hom(F, G)`, `I = Hom(F, F)` and `I' = Hom(G, G)` are algebraic spaces
affine and of finite presentation over the base, then so is the relative Isom functor
`Isom(F, G) = (H' ×_B H) ×_{c, I ×_B I', σ} B`. -/
theorem isAffineFinitePresentationAlgebraicSpaceOver_isomFunctor_of_homFunctors
    (h₁ : s.swap.IsAffineFinitePresentationAlgebraicSpaceOverBase hc)
    (h₂ : s.IsAffineFinitePresentationAlgebraicSpaceOverBase hc)
    (h₃ : s.endoSource.IsAffineFinitePresentationAlgebraicSpaceOverBase hc)
    (h₄ : s.endoTarget.IsAffineFinitePresentationAlgebraicSpaceOverBase hc) :
    IsAffineFinitePresentationAlgebraicSpaceOver s.base s.isomFunctor :=
  ((IsAffineFinitePresentationAlgebraicSpaceOver.prod h₁ h₂).sectionEqualizer
      (IsAffineFinitePresentationAlgebraicSpaceOver.prod h₃ h₄) (s.compositionNatTrans hc)
      s.identitySection (fun i => s.identitySection_naturality hc i)).of_iso
    ((s.mutualInverseFunctorIsoSectionEqualizer hc).symm ≪≫ s.mutualInverseFunctorIsoIsom)

end AlgebraicGeometry.Space.HomSituation

end
