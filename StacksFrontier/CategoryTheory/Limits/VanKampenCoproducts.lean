module

public import Mathlib.CategoryTheory.Limits.VanKampen
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Sites.LeftExact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Coproducts of sets, of presheaves and of sheaves of sets are van Kampen at any index

A coproduct is *van Kampen* when a cocone over a diagram mapping to it is colimiting exactly
when each of its squares is cartesian; this is the property that lets one decompose an object
lying over a coproduct summand by summand. Mathlib has it for *binary* coproducts of sets
(`CategoryTheory.types.finitaryExtensive`) and derives it for *finite* ones by induction on
`Fin n` (`CategoryTheory.FinitaryExtensive.isVanKampen_finiteCoproducts`), but not for an
arbitrary index type, where the induction is unavailable.

The set-theoretic content is elementary and index-free: the injections of a colimiting cofan
of types are injective, pairwise disjoint and jointly surjective, which is exactly what
cartesianness of the squares asserts fibre by fibre. That is
`CategoryTheory.isVanKampenColimit_of_isColimit_types` below, and the two transfer steps on
top of it are Mathlib's own and already hold at an arbitrary shape:

* `CategoryTheory.isVanKampenColimit_of_evaluation` carries the property from a coefficient
  category to a functor category, hence to presheaves;
* `CategoryTheory.IsVanKampenColimit.map_reflective` carries it along a reflective adjunction
  whose left adjoint is suitably exact, hence from presheaves to sheaves along sheafification.

## Main results

* `CategoryTheory.isVanKampenColimit_of_isColimit_types` and
  `CategoryTheory.isUniversalColimit_of_isColimit_types`: a colimiting cofan of types is van
  Kampen, and in particular universal, at an arbitrary index type.
* `CategoryTheory.isVanKampenColimit_of_isColimit_presheafOfTypes`: the same for presheaves
  of sets.
* `CategoryTheory.isVanKampenColimit_of_isColimit_sheafOfTypes` and
  `CategoryTheory.isUniversalColimit_of_isColimit_sheafOfTypes`: the same for sheaves of sets
  on a site admitting sheafification.

## Implementation notes

The index type is allowed to live in an arbitrary universe throughout the set-level
statements, since nothing there needs the coproduct to exist; the presheaf and sheaf
statements ask for the relevant coproducts as instance hypotheses instead.

The arbitrary diagram `F'` appearing in the definition of `CategoryTheory.IsVanKampenColimit`
is replaced by a `CategoryTheory.Discrete.functor` using `CategoryTheory.Functor.hext`, which
is the idiom Mathlib itself uses for discrete shapes; after that substitution the cocone over
it is literally a cofan and the three set-theoretic lemmas of
`Mathlib/CategoryTheory/Limits/Types/Coproducts.lean` apply.
-/

@[expose] public section

universe w u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Every functor out of a discrete category is equal to a `CategoryTheory.Discrete.functor`. -/
private theorem Discrete.exists_eq_functor {C : Type*} [Category* C] {I : Type w}
    (F : Discrete I ⥤ C) : ∃ X : I → C, F = Discrete.functor X :=
  ⟨F.obj ∘ Discrete.mk,
    Functor.hext (fun _ => rfl) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp)⟩

/-- **A colimiting cofan of types is van Kampen, at an arbitrary index type.**

Given a second family `X'` over `X` and a map `f` from a cocone point of `X'` to that of `X`
commuting with the injections, the cocone is colimiting precisely when every square is
cartesian: the three conditions characterising a cofan colimit of types — injectivity of each
injection, pairwise disjointness of their images, and joint surjectivity — correspond to
cartesianness fibrewise. -/
@[sga "4 II 4.5.1"]
theorem isVanKampenColimit_of_isColimit_types
    {I : Type w} {X : I → Type u} {c : Cofan X} (hc : IsColimit c) :
    IsVanKampenColimit c := by
  have hcinj : ∀ i, Function.Injective (Cofan.inj c i) :=
    Cofan.inj_injective_of_isColimit hc
  have hcdisj : ∀ (i j : I) (x : X i) (y : X j),
      Cofan.inj c i x = Cofan.inj c j y → i = j :=
    fun i j x y h => Cofan.eq_of_inj_apply_eq_of_isColimit hc x y h
  intro F' c' α f he _
  obtain ⟨X', rfl⟩ := Discrete.exists_eq_functor F'
  have hsq : ∀ i : I,
      Cofan.inj (f := X') c' i ≫ f = α.app ⟨i⟩ ≫ Cofan.inj c i :=
    fun i => (NatTrans.congr_app he ⟨i⟩).symm
  have hw : ∀ (i : I) (x : X' i),
      f (Cofan.inj (f := X') c' i x) = Cofan.inj c i (α.app ⟨i⟩ x) := fun i x => by
    simpa using ConcreteCategory.congr_hom (hsq i) x
  have hfw : ∀ (i j : I) (x : X' i) (y : X' j),
      Cofan.inj (f := X') c' i x = Cofan.inj c' j y →
        Cofan.inj c i (α.app ⟨i⟩ x) = Cofan.inj c j (α.app ⟨j⟩ y) :=
    fun i j x y hxy => ((hw i x).symm.trans (congrArg (fun z => f z) hxy)).trans (hw j y)
  constructor
  · rintro ⟨hc'⟩ ⟨i⟩
    rw [Limits.Types.isPullback_iff]
    refine ⟨hsq i, fun x y h => Cofan.inj_injective_of_isColimit hc' i h.1, fun z u hzu => ?_⟩
    obtain ⟨j, y, rfl⟩ := Cofan.inj_jointly_surjective_of_isColimit hc' z
    have key : Cofan.inj c j (α.app ⟨j⟩ y) = Cofan.inj c i u := (hw j y).symm.trans hzu
    obtain rfl : j = i := hcdisj j i _ u key
    exact ⟨y, rfl, hcinj j key⟩
  · intro h
    rw [← Cofan.isColimit_cofanTypes_iff]
    refine CofanTypes.isColimit_mk _ (fun z => ?_) (fun i x y hxy => ?_)
      (fun i j x y hxy => hcdisj i j _ _ (hfw i j x y hxy))
    · obtain ⟨i, u, hu⟩ := Cofan.inj_jointly_surjective_of_isColimit hc (f z)
      obtain ⟨x, hx, -⟩ := Limits.Types.exists_of_isPullback (h ⟨i⟩) z u hu.symm
      exact ⟨i, x, hx⟩
    · exact Limits.Types.ext_of_isPullback (h ⟨i⟩) hxy (hcinj i (hfw i i x y hxy))

/-- A colimiting cofan of types is a universal colimit, at an arbitrary index type. -/
@[sga "4 I 2.6" "special case"]
theorem isUniversalColimit_of_isColimit_types
    {I : Type w} {X : I → Type u} {c : Cofan X} (hc : IsColimit c) :
    IsUniversalColimit c :=
  (isVanKampenColimit_of_isColimit_types hc).isUniversal

/-- `CategoryTheory.isVanKampenColimit_of_isColimit_types` for a cocone over an arbitrary
diagram on a discrete category rather than over a `CategoryTheory.Discrete.functor`. -/
theorem isVanKampenColimit_of_isColimit_discreteTypes
    {I : Type w} {F : Discrete I ⥤ Type u} {c : Cocone F} (hc : IsColimit c) :
    IsVanKampenColimit c := by
  obtain ⟨X, rfl⟩ := Discrete.exists_eq_functor F
  exact isVanKampenColimit_of_isColimit_types hc

/-- **A colimiting coproduct of presheaves of sets is van Kampen, at an arbitrary index
type.** Van Kampen colimits in a functor category are detected objectwise, and
`CategoryTheory.isVanKampenColimit_of_evaluation` already holds at an arbitrary shape. -/
theorem isVanKampenColimit_of_isColimit_presheafOfTypes
    {C : Type*} [Category* C] {I : Type w} [HasColimitsOfShape (Discrete I) (Type u)]
    {F : Discrete I ⥤ (Cᵒᵖ ⥤ Type u)} {c : Cocone F} (hc : IsColimit c) :
    IsVanKampenColimit c :=
  isVanKampenColimit_of_evaluation F c fun _ =>
    isVanKampenColimit_of_isColimit_discreteTypes (isColimitOfPreserves _ hc)

/-- **A colimiting coproduct of sheaves of sets is van Kampen, at an arbitrary index type.**
Sheafification is a reflection whose left adjoint is left exact, and
`CategoryTheory.IsVanKampenColimit.map_reflective` already holds at an arbitrary shape, so the
property transfers from the coproduct of the underlying presheaves. -/
theorem isVanKampenColimit_of_isColimit_sheafOfTypes
    {C : Type*} [Category* C] (J : GrothendieckTopology C) [HasSheafify J (Type u)]
    {I : Type w} [HasColimitsOfShape (Discrete I) (Type u)]
    [HasColimitsOfShape (Discrete I) (Cᵒᵖ ⥤ Type u)]
    {F : Discrete I ⥤ Sheaf J (Type u)} {c : Cocone F} (hc : IsColimit c) :
    IsVanKampenColimit c := by
  have adj := sheafificationAdjunction J (Type u)
  apply (IsVanKampenColimit.precompose_isIso_iff
    (Functor.isoWhiskerLeft F (asIso adj.counit) ≪≫ Functor.rightUnitor F).hom).mp
  refine ((isVanKampenColimit_of_isColimit_presheafOfTypes
      (colimit.isColimit (F ⋙ sheafToPresheaf J (Type u)))).map_reflective adj).of_iso
    (IsColimit.uniqueUpToIso ?_ ?_)
  · exact isColimitOfPreserves _ (colimit.isColimit _)
  · exact (IsColimit.precomposeHomEquiv _ _).symm hc

/-- A colimiting coproduct of sheaves of sets is a universal colimit, at an arbitrary index
type. This is the form consumed when decomposing an object lying over such a coproduct. -/
@[sga "4 II 4.5.1" "partial"]
theorem isUniversalColimit_of_isColimit_sheafOfTypes
    {C : Type*} [Category* C] (J : GrothendieckTopology C) [HasSheafify J (Type u)]
    {I : Type w} [HasColimitsOfShape (Discrete I) (Type u)]
    [HasColimitsOfShape (Discrete I) (Cᵒᵖ ⥤ Type u)]
    {F : Discrete I ⥤ Sheaf J (Type u)} {c : Cocone F} (hc : IsColimit c) :
    IsUniversalColimit c :=
  (isVanKampenColimit_of_isColimit_sheafOfTypes J hc).isUniversal

end CategoryTheory

end
