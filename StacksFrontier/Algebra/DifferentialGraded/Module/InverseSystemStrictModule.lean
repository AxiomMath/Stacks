module

public import StacksFrontier.Algebra.DifferentialGraded.Module.InverseSystemStrict

/-!
# Strict inverse systems of differential graded modules

Let `(A_n)` be a strict inverse system of differential graded algebras, so that its transition
homomorphisms compose on the nose. A *strict* inverse system of differential graded modules over
it is a module `N_n` over `A_n` for every `n` together with a homomorphism `N_m ⟶ N_n|_{A_m}` for
every `n ≤ m` whose underlying linear maps compose. Reading each `N_n` in the derived category of
`A_n` and each transition homomorphism through `DifferentialGradedModule.derivedTrans` gives an
inverse system of differential graded modules in the sense of
`DifferentialGraded.ModuleSystem`, which is what Tag 0GZI applies to.

## Main definitions

* `DifferentialGraded.StrictModuleSystem`: a strict inverse system of differential graded modules
  over a strict inverse system of differential graded algebras.
* `DifferentialGraded.StrictModuleSystem.toModuleSystem`: the inverse system of differential
  graded modules, levelwise in the derived category, that it gives.

## Main results

* `DifferentialGradedModule.derivedTrans_comp`: two homomorphisms of differential graded modules
  whose composite is a third one give maps in the derived categories whose composite, compared
  along `DifferentialGradedModule.derivedRestrictionComp`, is the map of the third. This is the
  one compatibility that `DifferentialGraded.ModuleSystem` asks for.

## Implementation notes

The identity above is proved through `DifferentialGradedModule.derivedTrans_comp_aux`, which
states it for abstract categories and abstract comparison isomorphisms. Stated directly in a
localized category the two sides of a composition are presented at different instance paths for
`CategoryTheory.Quiver.Hom`, and `CategoryTheory.Category.assoc` then refuses to rewrite; over
abstract categories that does not arise, and the concrete statement follows by definitional
unfolding. For the same reason the identification of the composite transition homomorphism is
taken as a separate argument, to be substituted away before any rewriting, and the component of
`DifferentialGraded.AlgebraSystem.restrComp` for a strict system is computed by
`DifferentialGraded.StrictAlgebraSystem.toAlgebraSystem_restrComp_hom_app` rather than left to
conversion. The object at which the comparison is evaluated, the comparison itself and the maps
being composed are parameters of `DifferentialGradedModule.derivedTrans_comp` rather than
computed from the modules: a component of the comparison evaluated at two names for one object
is not recognised by conversion within any reasonable bound, so the statement must be usable at
the names its consumer already has.

## References

* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX)
* [Stacks Project, Tag 0GZI](https://stacks.math.columbia.edu/tag/0GZI)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGradedModule

/-- Two factorizations of a functor through localizations, composed and compared with a third:
the generic shape of the compatibility that a two-step restriction of scalars satisfies, stated
for abstract categories. -/
theorem derivedTrans_comp_aux {H₁ H₂ H₃ D₁ D₂ D₃ : Type*} [Category H₁] [Category H₂]
    [Category H₃] [Category D₁] [Category D₂] [Category D₃]
    {Q₁ : H₁ ⥤ D₁} {Q₂ : H₂ ⥤ D₂} {Q₃ : H₃ ⥤ D₃}
    {R₁₂ : H₂ ⥤ H₁} {R₂₃ : H₃ ⥤ H₂} {R₁₃ : H₃ ⥤ H₁}
    {F₁₂ : D₂ ⥤ D₁} {F₂₃ : D₃ ⥤ D₂} {F₁₃ : D₃ ⥤ D₁}
    (f₁₂ : Q₂ ⋙ F₁₂ ≅ R₁₂ ⋙ Q₁) (f₂₃ : Q₃ ⋙ F₂₃ ≅ R₂₃ ⋙ Q₂)
    (f₁₃ : Q₃ ⋙ F₁₃ ≅ R₁₃ ⋙ Q₁) (e : R₂₃ ⋙ R₁₂ = R₁₃)
    {X₁ : H₁} {X₂ : H₂} {X₃ : H₃}
    (a : X₁ ⟶ R₁₂.obj X₂) (b : X₂ ⟶ R₂₃.obj X₃) (c : X₁ ⟶ R₁₃.obj X₃)
    (hc : a ≫ R₁₂.map b ≫ eqToHom (congrArg (fun F : H₃ ⥤ H₁ => F.obj X₃) e) = c) :
    (Q₁.map a ≫ f₁₂.inv.app X₂) ≫
        F₁₂.map (Q₂.map b ≫ f₂₃.inv.app X₃) ≫
          F₁₂.map (f₂₃.hom.app X₃) ≫ f₁₂.hom.app (R₂₃.obj X₃) ≫
            (eqToIso (congrArg (fun F : H₃ ⥤ H₁ => F ⋙ Q₁) e)).hom.app X₃ ≫ f₁₃.inv.app X₃ =
      Q₁.map c ≫ f₁₃.inv.app X₃ := by
  subst e
  simp only [eqToHom_refl, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Functor.comp_obj,
    Category.comp_id, Category.id_comp] at hc ⊢
  subst hc
  have hnat : Q₁.map (R₁₂.map b) ≫ f₁₂.inv.app (R₂₃.obj X₃) =
      f₁₂.inv.app X₂ ≫ F₁₂.map (Q₂.map b) := f₁₂.inv.naturality b
  rw [F₁₂.map_comp]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.comp_obj,
    Category.comp_id]
  rw [← reassoc_of% hnat, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc]

variable {R : Type u} [CommRing R] {A B C : DifferentialGradedAlgebra.{u, u} R}

/-- **The maps of composable homomorphisms of differential graded modules compose.** If
`v : M ⟶ N|_A` and `w : N ⟶ P|_B` compose to `t : M ⟶ P|_A` over an identification of `ψ ∘ φ`
with `χ`, then the maps `DifferentialGradedModule.derivedTrans` of `v` and of `w`, composed and
compared along `DifferentialGradedModule.derivedRestrictionComp`, are the map of `t`. The object
of the derived category, the comparison isomorphism and the two latter maps are taken as
parameters together with the identifications they satisfy, so that the statement can be used at
whatever presentation of them is at hand. -/
theorem derivedTrans_comp (φ : A.Hom B) (ψ : B.Hom C) (χ : A.Hom C) (e : ψ.comp φ = χ)
    {M : DifferentialGradedModule.{u, u, u} A} {N : DifferentialGradedModule.{u, u, u} B}
    {P : DifferentialGradedModule.{u, u, u} C}
    (v : M ⟶ restrictScalars φ N) (w : N ⟶ restrictScalars ψ P)
    (t : M ⟶ restrictScalars χ P)
    (ht : v ≫ (restrictScalarsFunctor φ).map w ≫
      eqToHom (congrArg (fun α : A.Hom C => restrictScalars α P) e) = t)
    (Z : derivedCategory' C)
    (hZ : (quasiIsomorphisms' C).Q.obj ((toHomotopyCategory C).obj P) = Z)
    {cmp : derivedRestriction ψ ⋙ derivedRestriction φ ≅ derivedRestriction χ}
    (hcmp : ∀ X : derivedCategory' C, cmp.hom.app X =
      (derivedRestrictionComp φ ψ).hom.app X ≫
        (eqToIso (congrArg (fun α : A.Hom C => derivedRestriction α) e)).hom.app X)
    (p : (quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj M) ⟶
      (derivedRestriction φ).obj ((quasiIsomorphisms' B).Q.obj ((toHomotopyCategory B).obj N)))
    (hp : derivedTrans φ v = p)
    (q : (quasiIsomorphisms' B).Q.obj ((toHomotopyCategory B).obj N) ⟶
      (derivedRestriction ψ).obj Z)
    (hq : HEq (derivedTrans ψ w) q)
    (r : (quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj M) ⟶
      (derivedRestriction χ).obj Z)
    (hr : HEq (derivedTrans χ t) r) :
    p ≫ (derivedRestriction φ).map q ≫ cmp.hom.app Z = r := by
  subst e
  subst hZ
  subst hp
  obtain rfl : derivedTrans ψ w = q := eq_of_heq hq
  obtain rfl : derivedTrans (ψ.comp φ) t = r := eq_of_heq hr
  rw [hcmp]
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id] at ht ⊢
  subst ht
  have idh : ∀ {X Y : HomotopyCategory A} (f : X ⟶ Y) (p : Y = Y), f ≫ eqToHom p = f :=
    fun f p => by rw [eqToHom_refl, Category.comp_id]
  have hc : (toHomotopyCategory A).map v ≫
        (restrictScalarsHomotopyFunctor φ).map ((toHomotopyCategory B).map w) ≫
          eqToHom (congrArg (fun F : HomotopyCategory C ⥤ HomotopyCategory A =>
            F.obj ((toHomotopyCategory C).obj P)) (restrictScalarsHomotopyFunctor_comp φ ψ)) =
      (toHomotopyCategory A).map (v ≫ (restrictScalarsFunctor φ).map w) :=
    (congrArg (fun z => (toHomotopyCategory A).map v ≫ z) (idh _ _)).trans
      ((toHomotopyCategory A).map_comp v ((restrictScalarsFunctor φ).map w)).symm
  rw [derivedRestrictionComp_hom_app]
  exact derivedTrans_comp_aux (derivedRestrictionFactorization φ)
    (derivedRestrictionFactorization ψ) (derivedRestrictionFactorization (ψ.comp φ))
    (restrictScalarsHomotopyFunctor_comp φ ψ) ((toHomotopyCategory A).map v)
    ((toHomotopyCategory B).map w) _ hc

end DifferentialGradedModule

namespace DifferentialGraded

open DifferentialGradedModule

variable {R : Type u} [CommRing R]

namespace StrictAlgebraSystem

/-- The identification of a two-step restriction of scalars with a one-step one, for the inverse
system underlying a strict one: the comparison for a composite, followed by the identification of
the composite transition homomorphism with the one-step one. -/
theorem toAlgebraSystem_restrComp_hom_app (T : StrictAlgebraSystem R) {n m k : ℕ}
    (h : n ≤ m) (h' : m ≤ k) (X : derivedCategory' (T.alg n)) :
    (T.toAlgebraSystem.restrComp h h').hom.app X =
      (derivedRestrictionComp (T.trans h') (T.trans h)).hom.app X ≫
        (eqToIso (congrArg (fun α : (T.alg k).Hom (T.alg n) => derivedRestriction α)
          (T.trans_comp h h'))).hom.app X := by
  rw [show T.toAlgebraSystem.restrComp h h' =
      derivedRestrictionComp (T.trans h') (T.trans h) ≪≫
        eqToIso (congrArg (fun α : (T.alg k).Hom (T.alg n) => derivedRestriction α)
          (T.trans_comp h h')) from rfl, Iso.trans_hom, NatTrans.comp_app]

end StrictAlgebraSystem

/-- **A strict inverse system of differential graded modules** over a strict inverse system of
differential graded algebras: a module `N_n` over `A_n` for every `n` and a homomorphism
`N_m ⟶ N_n|_{A_m}` for every `n ≤ m`, composing on the nose. -/
structure StrictModuleSystem (T : StrictAlgebraSystem R) where
  /-- The differential graded `A_n`-module `N_n` of the system. -/
  mod : ∀ n : ℕ, DifferentialGradedModule.{u, u, u} (T.alg n)
  /-- The transition homomorphism `N_m ⟶ N_n|_{A_m}` of the system, for `n ≤ m`. -/
  trans : ∀ {n m : ℕ} (h : n ≤ m), mod m ⟶ restrictScalars (T.trans h) (mod n)
  /-- The transition homomorphisms compose, over the composition of the transition homomorphisms
  of the system of algebras. -/
  trans_comp : ∀ {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k),
    trans h' ≫ (restrictScalarsFunctor (T.trans h')).map (trans h) ≫
        eqToHom (congrArg (fun α : (T.alg k).Hom (T.alg n) => restrictScalars α (mod n))
          (T.trans_comp h h')) =
      trans (h.trans h')

namespace StrictModuleSystem

variable {T : StrictAlgebraSystem R} (N : StrictModuleSystem T)

/-- The `n`-th module of a strict system, read in the derived category of `A_n`. -/
def derivedObj (n : ℕ) : derivedCategory' (T.alg n) :=
  (quasiIsomorphisms' (T.alg n)).Q.obj ((toHomotopyCategory (T.alg n)).obj (N.mod n))

/-- The transition homomorphism of a strict system, read as a map `N_m ⟶ N_n|_{A_m}` in the
derived category of `A_m`. -/
def derivedMap {n m : ℕ} (h : n ≤ m) :
    N.derivedObj m ⟶ (T.toAlgebraSystem.restr h).obj (N.derivedObj n) :=
  derivedTrans (T.trans h) (N.trans h)

/-- The transition maps in the derived category compose, over the identification of a two-step
restriction of scalars with a one-step one. -/
theorem derivedMap_derivedMap {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k) :
    N.derivedMap (h.trans h') =
      N.derivedMap h' ≫ (T.toAlgebraSystem.restr h').map (N.derivedMap h) ≫
        (T.toAlgebraSystem.restrComp h h').hom.app (N.derivedObj n) :=
  (derivedTrans_comp (T.trans h') (T.trans h) (T.trans (h.trans h')) (T.trans_comp h h')
    (N.trans h') (N.trans h) (N.trans (h.trans h')) (N.trans_comp h h') (N.derivedObj n) rfl
    (T.toAlgebraSystem_restrComp_hom_app h h') (N.derivedMap h') rfl (N.derivedMap h) HEq.rfl
    (N.derivedMap (h.trans h')) HEq.rfl).symm

/-- The inverse system of differential graded modules underlying a strict one: every module is
read in the derived category and every transition homomorphism through
`DifferentialGradedModule.derivedTrans`. -/
def toModuleSystem : ModuleSystem T.toAlgebraSystem where
  obj := N.derivedObj
  trans := N.derivedMap
  trans_trans := N.derivedMap_derivedMap

/-- The `n`-th object of `N.toModuleSystem` is `N.derivedObj n`. -/
@[simp] theorem toModuleSystem_obj (n : ℕ) : N.toModuleSystem.obj n = N.derivedObj n := rfl

/-- The transition map of `N.toModuleSystem` for `n ≤ m` is `N.derivedMap h`. -/
@[simp] theorem toModuleSystem_trans {n m : ℕ} (h : n ≤ m) :
    N.toModuleSystem.trans h = N.derivedMap h := rfl

end StrictModuleSystem

end DifferentialGraded

end
