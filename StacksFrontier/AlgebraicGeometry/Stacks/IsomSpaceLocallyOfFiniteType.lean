module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalLocallyOfFiniteType
public import StacksFrontier.CategoryTheory.Sites.Stack.IsomPresheafVertHom

/-!
# The isomorphism spaces of a limit preserving category fibred in groupoids

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S`, with object
and morphism universes independent of the site's. If `𝒳` is limit preserving (Stacks 07XL),
then every algebraic space representing an isomorphism presheaf `Isom(a, b)` of two objects of
`𝒳` over a scheme `T` is locally of finite type over `T`.

This is Stacks 0CXI, "the diagonal of a limit preserving `𝒳` is locally of finite type", read
on the base changes of the diagonal along points `(a, b)` of `𝒳 × 𝒳`, which are exactly the
isomorphism presheaves; it is the form in which Stacks 0CXM asks for local finite type of the
diagonal.

## Main results

* `AlgebraicGeometry.Stack.isLocallyOfFiniteType_toYonedaId_of_diagonalFibre`: the local step,
  for the presheaf of vertical morphisms between the two components of a point of `𝒳 × 𝒳`.
* `AlgebraicGeometry.Stack.isLocallyOfFiniteType_isomSpace_of_isLimitPreserving`: the
  isomorphism-sheaf form.

## Implementation notes

The local step is the argument of `AlgebraicGeometry.Stack.isLocallyOfFiniteType_diagonal`, run
over the base `T` of the point directly: the surjectivity criterion of Stacks 0CM6 asks that every
vertical morphism over an affine inverse limit descend to a stage, which is the fullness half of
limit preservation. No reduction to affine bases (Stacks 07WI) is needed, so the universes of `𝒳`
stay free.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))

open TwoFibreProductOver.DiagonalFibre in
/-- **The local step of Stacks 0CXI.** Let `y` be a point of `𝒳 × 𝒳` over a scheme `U`, and let
`F` be an algebraic space over `U` representing the base change of the diagonal along `y`. If
`𝒳` is limit preserving, then `F` is locally of finite type over `U`. -/
theorem isLocallyOfFiniteType_toYonedaId_of_diagonalFibre
    (h𝒳 : Deformation.Artin.IsLimitPreserving.{u, u, u, w, v} B S hS 𝒳)
    (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ TwoFibreProductOver 𝒳.val.p 𝒳.val.p
      (𝟭 (BigFppfOver B S hS)) 𝒳.val.p 𝒳.val.p)
    (hy : y ⋙ ProdP 𝒳.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (eF : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p (ProdP 𝒳.val.p) y (Diag 𝒳.val.p))
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    Space.IsLocallyOfFiniteType B U.left.1 U.left.2 (Space.toYonedaId B U.left.1 U.left.2 F) := by
  classical
  refine Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B U.left.1 U.left.2 ?_
  refine Space.isLocallyOfFinitePresentation_of_affineLimit_surjective B U.left.1 U.left.2 hF
    (isAlgebraicSpace_yoneda B U.left.1 U.left.2 _)
    (Space.toYonedaId B U.left.1 U.left.2 F) ?_
  intro I _ _ D c hc hDaff hcaff x yy _hxy
  have : Nonempty I := IsCofiltered.nonempty
  have hp := 𝒳.isFiberedInGroupoids
  have hfib : 𝒳.val.p.IsFibered := hp.isFibered
  obtain ⟨e⟩ := (nonempty_equivalenceOver_fst_iff hp hy F).mp ⟨eF⟩
  let pe := PresheafOfCategories.PointwiseEquiv.ofUliftIso e
  have haff : ∀ i, IsAffineOver B S hS ((D ⋙ Over.map U.hom).obj i) := fun i => hDaff i
  have hcaff' : IsAffineOver B S hS ((Over.map U.hom).obj c.pt) := hcaff
  set D' : I ⥤ BigAffineFppf B S hS :=
    (IsAffineOver B S hS).lift (D ⋙ Over.map U.hom) haff with hD'def
  set c' : Cone D' :=
    { pt := ⟨(Over.map U.hom).obj c.pt, hcaff'⟩
      π :=
        { app := fun i => ObjectProperty.homMk ((Over.map U.hom).map (c.π.app i))
          naturality := fun i j f => by
            apply ObjectProperty.hom_ext
            change 𝟙 _ ≫ (Over.map U.hom).map (c.π.app j) =
              (Over.map U.hom).map (c.π.app i) ≫ (Over.map U.hom).map (D.map f)
            rw [Category.id_comp, ← Functor.map_comp, c.w f] } } with hc'def
  have hc' : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c') := hc
  have : (Deformation.Artin.colimitComparison 𝒳.val.p
      (D' ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c')).Full := (h𝒳 I D' c' hc').full
  have hdesc : Deformation.Artin.DescentHom 𝒳.val.p (D ⋙ Over.map U.hom)
      ((Over.map U.hom).mapCone c) :=
    Deformation.Artin.descentHom_of_full 𝒳.val.p hp
      (D' ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c')
  obtain ⟨k, χ, hχ⟩ :=
    TwoFibreProductOver.DiagonalFibre.VertHom.exists_restrict_eq_of_descentHom hp
      (TwoFibreProductOver.DiagonalFibre.h1' hy) (TwoFibreProductOver.DiagonalFibre.h2' hy)
      D c hdesc ((pe.equiv (op c.pt)).symm x)
  refine ⟨colimit.ι (D.op ⋙ F) (op k) (pe.equiv (op (D.obj k)) χ), ?_, ?_⟩
  · rw [colimit.ι_desc_apply]
    refine Eq.trans ?_ ((pe.equiv (op c.pt)).apply_symm_apply x)
    rw [← hχ, ← TwoFibreProductOver.DiagonalFibre.VertHom.presheaf_map]
    exact (pe.naturality (c.π.app k).op χ).symm
  · have : Subsingleton (colimit (D.op ⋙ yoneda.obj (Over.mk (𝟙 (B.obj U.left.2))))) := by
      have hsub : ∀ {J : Type u} [Category.{u} J] [IsFiltered J] (G : J ⥤ Type u)
          [HasColimit G], (∀ j, Subsingleton (G.obj j)) → Subsingleton (colimit G) := by
        intro J _ _ G _ hG
        refine ⟨fun a b => ?_⟩
        obtain ⟨i, x, rfl⟩ := Types.jointly_surjective' a
        obtain ⟨j, y, rfl⟩ := Types.jointly_surjective' b
        rw [← colimit.w_apply (F := G) (IsFiltered.leftToMax i j) x,
          ← colimit.w_apply (F := G) (IsFiltered.rightToMax i j) y,
          (hG (IsFiltered.max i j)).elim (G.map (IsFiltered.leftToMax i j) x)
            (G.map (IsFiltered.rightToMax i j) y)]
      refine hsub _ (fun j => ?_)
      exact ⟨fun a b => Over.mkIdTerminal.hom_ext a b⟩
    exact this.elim _ _

open TwoFibreProductOver.DiagonalFibre in
/-- **Stacks 0CXI, the isomorphism-sheaf form.** If `𝒳` is limit preserving, then for any two
objects `a`, `b` of `𝒳` over a scheme `T`, every algebraic space over `T` representing the
isomorphism presheaf `Isom(a, b)` is locally of finite type over `T`. -/
theorem isLocallyOfFiniteType_isomSpace_of_isLimitPreserving
    (h𝒳 : Deformation.Artin.IsLimitPreserving.{u, u, u, w, v} B S hS 𝒳) :
    letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
    ∀ (T : BigFppfOver B S hS) (a b : 𝒳.val.p.Fiber T)
      (G : (BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u),
      IsAlgebraicSpace B T.left.1 T.left.2 G →
      Nonempty (G ⋙ uliftFunctor.{v, u} ≅
        ((Over.iteratedSliceBackward T).op ⋙ 𝒳.val.p.isomPresheaf a b) ⋙
          uliftFunctor.{u, v}) →
      Space.IsLocallyOfFiniteType B T.left.1 T.left.2
        (terminal.from G : G ⟶ ⊤_ ((BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u)) := by
  have hp := 𝒳.isFiberedInGroupoids
  have hpf : 𝒳.val.p.IsFibered := hp.isFibered
  intro T a b G hG ⟨i⟩
  have h₁ := Functor.backward_pullbackSliceFunctor_comp 𝒳.val.p T a
  have h₂ := Functor.backward_pullbackSliceFunctor_comp 𝒳.val.p T b
  have hY : pairFunctor h₁ h₂ ⋙ ProdP 𝒳.val.p = Over.map T.hom := pairFunctor_comp h₁ h₂
  have c : vertHomPresheaf hp hY ≅
      (Over.iteratedSliceBackward T).op ⋙ 𝒳.val.p.isomPresheaf a b :=
    Functor.vertHomPresheafIsoIsomPresheaf 𝒳.val.p T a b hp
  have hE : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map T.hom) 𝒳.val.p (ProdP 𝒳.val.p)
        (pairFunctor h₁ h₂) (Diag 𝒳.val.p))
      (presheafOfCategories (G ⋙ typeToCat)).p) :=
    (nonempty_equivalenceOver_fst_iff hp hY G).2
      ⟨(Functor.isoWhiskerRight c uliftFunctor.{u, v}).trans i.symm⟩
  have hlft := isLocallyOfFiniteType_toYonedaId_of_diagonalFibre B S hS 𝒳 h𝒳 T
    (pairFunctor h₁ h₂) hY G hG hE.some
  exact Space.holdsOnEveryEtaleChart_of_isTerminal B T.left.1 T.left.2
    (Over.mkIdTerminal.isTerminalObj yoneda _) terminalIsTerminal _ _ hlft

end AlgebraicGeometry.Stack

end
