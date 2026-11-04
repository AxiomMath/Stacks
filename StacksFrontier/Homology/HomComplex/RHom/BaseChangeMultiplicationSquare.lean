module

public import StacksFrontier.Homology.HomComplex.RHom.BaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# The multiplication square of a derived-Hom base-change map

Let `R → R'` be a ring map, let `bc ⊣ res` be the adjunction between derived extension of
scalars and derived restriction of scalars, and write `μ = ε` for the counit of that adjunction,
the *multiplication map* `K' ⊗^𝐋_R R' ⟶ K'` of an object `K'` of `D(R')` read on its underlying
object of `D(R)`.  The base-change map for derived Hom is by construction the transpose of a
comparison map along `bc ⊣ res`, and this module proves the compatibility of that transpose with
the multiplication map: the square

```
RHom(M, Q L) ⊗^𝐋_R R'  ---β--->  RHom'(P M, P Q L)
        |                              |
        μ                              a
        v                              v
RHom(M, Q L)           ---Φ--->  RHom'(P M, L)
```

commutes, where `P ⊣ Q` is a second adjunction (in the geometric situation `P = L(g')^*` and
`Q = Rg'_*`), `a` is induced by its counit, `Φ` is the change-of-rings identification
`RHom(M, Q L) ≅ res RHom'(P M, L)`, and `β` is the transpose of
`RHom(M, Q L) ⟶ RHom(M, Q P Q L) ≅ res RHom'(P M, P Q L)`.

## Main results

* `Stacks.DerivedHom.BaseChange.transposedComparison_comp_counit`: the square above, with `β`
  spelled out as the transpose.  No hypotheses beyond the data of the two adjunctions, the two
  Hom bifunctors and the identification `Φ`.
* `Stacks.DerivedHom.BaseChange.comparison_comp_counit`: the same square for any morphism `β`
  whose transpose is that comparison — the form in which a construction of `β` elsewhere feeds
  into the square.
* `Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_restrictScalars_comp_counit`: the
  square for the derived-module base-change map of Stacks 0E1X, with `P ⊣ Q` the derived
  extension/restriction adjunction itself and `Φ` the change-of-rings isomorphism of
  Stacks 0E1W.

## Implementation notes

Both adjunctions are needed because in the geometric statement they are different: the ring-level
adjunction `- ⊗^𝐋_R R' ⊣ res` is what the transpose is taken along, while the adjunction whose
unit and counit appear inside the Hom bifunctors is `L(g')^* ⊣ Rg'_*` on the derived categories of
modules on the two schemes.  The algebraic statement is the case where the two coincide.

The proof is the transposition argument and nothing else: applying the ring-level adjunction
bijection turns the right-hand vertical arrow into `res` of itself by
`CategoryTheory.Adjunction.homEquiv_naturality_right_symm`, the naturality of `Φ` in its
covariant variable moves it past the identification, and the two unit/counit factors that remain
cancel by the triangle identity `CategoryTheory.Adjunction.right_triangle_components` of the
*second* adjunction.  So the mathematical content is exactly that triangle identity for `P ⊣ Q`
together with the naturality of `Φ`.

*The geometric square.*  The geometric statement of Stacks 0BZA is this square for `M, L`
objects of the derived categories of modules on the schemes `X`, `X'` of a Tor-independent
base-change square with affine base `S = Spec R`, `S' = Spec R'`, with `RHom_X(-, -)` the global
derived Hom read in `D(R)` and `β` the base-change map of Stacks 0AA7; it is
`AlgebraicGeometry.GlobalHomBaseChange.globalHomBaseChangeMap_comp_counit`.

## References

* [Stacks Project, Tag 0BZA](https://stacks.math.columbia.edu/tag/0BZA)
* [Stacks Project, Tag 0AA7](https://stacks.math.columbia.edu/tag/0AA7)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace Stacks.DerivedHom.BaseChange

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {S : Type u₃} [Category.{v₃} S] {T : Type u₄} [Category.{v₄} T]

/-- **The multiplication square, with the base-change map spelled out as a transpose.**

Let `adj : F ⊣ G` and `adj' : P ⊣ Q` be adjunctions, let `HS : Sᵒᵖ × S ⥤ C` and
`HT : Tᵒᵖ × T ⥤ D` be Hom-like bifunctors and let

`Φ : HS(-, Q -) ≅ G (HT(P -, -))`

be an identification of them under `adj'`.  Transposing

`HS(M, Q L) ⟶ HS(M, Q P Q L) ⟶ G (HT(P M, P Q L))`,

the unit of `adj'` followed by `Φ`, gives a map `F (HS(M, Q L)) ⟶ HT(P M, P Q L)`.  Following it
by the map induced by the counit of `adj'` gives the same result as applying `F` to `Φ` and then
the counit of `adj`.

With `F = - ⊗^𝐋_R R'`, `G` restriction of scalars, `P = L(g')^*` and `Q = Rg'_*`, the counit of
`adj` is the multiplication map and this is the square of Stacks 0BZA. -/
public theorem transposedComparison_comp_counit {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {P : S ⥤ T} {Q : T ⥤ S} (adj' : P ⊣ Q)
    {HS : Sᵒᵖ × S ⥤ C} {HT : Tᵒᵖ × T ⥤ D}
    (Φ : (𝟭 Sᵒᵖ).prod Q ⋙ HS ≅ P.op.prod (𝟭 T) ⋙ HT ⋙ G) (M : S) (L : T) :
    (adj.homEquiv (HS.obj (op M, Q.obj L)) (HT.obj (op (P.obj M), P.obj (Q.obj L)))).symm
          (HS.map (X := (op M, Q.obj L)) (Y := (op M, Q.obj (P.obj (Q.obj L))))
              (𝟙 (op M), adj'.unit.app (Q.obj L)) ≫
            Φ.hom.app (op M, P.obj (Q.obj L))) ≫
        HT.map (X := (op (P.obj M), P.obj (Q.obj L))) (Y := (op (P.obj M), L))
          (𝟙 (op (P.obj M)), adj'.counit.app L) =
      F.map (Φ.hom.app (op M, L)) ≫ adj.counit.app (HT.obj (op (P.obj M), L)) := by
  rw [← adj.homEquiv_naturality_right_symm, Adjunction.homEquiv_counit]
  congr 1
  have hnat : HS.map (X := (op M, Q.obj (P.obj (Q.obj L)))) (Y := (op M, Q.obj L))
        (𝟙 (op M), Q.map (adj'.counit.app L)) ≫ Φ.hom.app (op M, L) =
      Φ.hom.app (op M, P.obj (Q.obj L)) ≫
        G.map (HT.map (X := (op (P.obj M), P.obj (Q.obj L))) (Y := (op (P.obj M), L))
          (𝟙 (op (P.obj M)), adj'.counit.app L)) := by
    simpa using Φ.hom.naturality (X := (op M, P.obj (Q.obj L))) (Y := (op M, L))
      (𝟙 (op M), adj'.counit.app L)
  rw [Category.assoc, ← hnat, ← Category.assoc, ← Functor.map_comp]
  have hcancel : ((𝟙 (op M), adj'.unit.app (Q.obj L)) :
        ((op M, Q.obj L) : Sᵒᵖ × S) ⟶ (op M, Q.obj (P.obj (Q.obj L)))) ≫
        ((𝟙 (op M), Q.map (adj'.counit.app L)) :
          ((op M, Q.obj (P.obj (Q.obj L))) : Sᵒᵖ × S) ⟶ (op M, Q.obj L)) =
        𝟙 (op M, Q.obj L) := by
    ext <;> simp
  rw [hcancel, HS.map_id, Category.id_comp]

/-- **The multiplication square** for any morphism `β` characterised by its transpose, which is
the form in which a separately constructed base-change map feeds into
`Stacks.DerivedHom.BaseChange.transposedComparison_comp_counit`. -/
public theorem comparison_comp_counit {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {P : S ⥤ T} {Q : T ⥤ S} (adj' : P ⊣ Q)
    {HS : Sᵒᵖ × S ⥤ C} {HT : Tᵒᵖ × T ⥤ D}
    (Φ : (𝟭 Sᵒᵖ).prod Q ⋙ HS ≅ P.op.prod (𝟭 T) ⋙ HT ⋙ G) (M : S) (L : T)
    (β : F.obj (HS.obj (op M, Q.obj L)) ⟶ HT.obj (op (P.obj M), P.obj (Q.obj L)))
    (hβ : adj.homEquiv _ _ β =
      HS.map (X := (op M, Q.obj L)) (Y := (op M, Q.obj (P.obj (Q.obj L))))
          (𝟙 (op M), adj'.unit.app (Q.obj L)) ≫
        Φ.hom.app (op M, P.obj (Q.obj L))) :
    β ≫ HT.map (X := (op (P.obj M), P.obj (Q.obj L))) (Y := (op (P.obj M), L))
          (𝟙 (op (P.obj M)), adj'.counit.app L) =
      F.map (Φ.hom.app (op M, L)) ≫ adj.counit.app (HT.obj (op (P.obj M), L)) := by
  rw [(adj.homEquiv _ _).eq_symm_apply.2 hβ]
  exact transposedComparison_comp_counit adj adj' Φ M L

end Stacks.DerivedHom.BaseChange

namespace Stacks.DerivedHom.ExtensionOfScalars

universe uR uA uM

attribute [local instance] HasDerivedCategory.standard

/-- **The multiplication square for the derived-module base-change map of Stacks 0E1X.**

For a ring map `f : R → A`, `K ∈ D(R)` and `N ∈ D(A)`, write `bc` for a total left-derived
extension of scalars and `res` for derived restriction of scalars.  The base-change map

`bc (RHom_R(K, res N)) ⟶ RHom_A(bc K, bc (res N))`

of Stacks 0E1X followed by the map induced by the counit `bc (res N) ⟶ N` agrees with `bc` of the
change-of-rings isomorphism `RHom_R(K, res N) ≅ res RHom_A(bc K, N)` of Stacks 0E1W followed by
the counit of the adjunction at `RHom_A(bc K, N)`, i.e. by the multiplication map.

This is the affine, algebraic avatar of the square of Stacks 0BZA: there `R → A` is `R → R'`, the
counit of the adjunction is the multiplication map `K' ⊗^𝐋_R R' ⟶ K'`, and the lower horizontal
identification is the change-of-rings isomorphism.  The geometric statement, over a general
quasi-compact and quasi-separated `X`, is
`AlgebraicGeometry.GlobalHomBaseChange.globalHomBaseChangeMap_comp_counit`. -/
public theorem derivedHomBaseChange_restrictScalars_comp_counit
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A) :
    (letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    ∀ (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (K : DerivedCategory (ModuleCat.{max uR uA uM} R))
    (N : DerivedCategory (ModuleCat.{max uR uA uM} A)),
    derivedHomBaseChange.{uR, uA, uM} f F comparison K
          ((ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.obj N) ≫
        (ScalarTransportedInternalHom.hom.{uA, max uR uA uM} A).map
          (X := (op (F.obj K),
            F.obj ((ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.obj N)))
          (Y := (op (F.obj K), N))
          (𝟙 (op (F.obj K)),
            (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, uM}
              f F comparison).counit.app N) =
      F.map ((BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
            comparison).hom.app (op K, N)) ≫
        (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, uM}
            f F comparison).counit.app
          ((ScalarTransportedInternalHom.hom.{uA, max uR uA uM} A).obj (op (F.obj K), N))) := by
  intro F comparison _ K N
  exact BaseChange.comparison_comp_counit
    (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, uM}
      f F comparison)
    (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, uM}
      f F comparison)
    (BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F comparison) K N
    (derivedHomBaseChange.{uR, uA, uM} f F comparison K _)
    (derivedHomBaseChange_homEquiv.{uR, uA, uM} f F comparison K _)

end Stacks.DerivedHom.ExtensionOfScalars

end
