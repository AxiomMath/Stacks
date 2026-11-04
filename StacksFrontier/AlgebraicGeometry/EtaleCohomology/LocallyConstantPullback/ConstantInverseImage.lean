module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Limits.Types.Products
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-!
# The inverse image of a constant sheaf of sets is constant

Let `f : Sh(C, J) ⟶ Sh(D, K)` be a morphism of topoi, i.e. an adjoint pair `f⁻¹ ⊣ f_*` with
`f⁻¹` left exact. If both sites have a final object then `f⁻¹` carries the constant sheaf on a
set `E` to the constant sheaf on `E`, so it carries constant sheaves to constant sheaves.

The proof is by uniqueness of left adjoints and never touches the construction of sheafification,
which is why it holds for a carrier universe unrelated to the site. Writing `Γ_C` for the sections
over the final object of `C`, the constant sheaf functor is left adjoint to `Γ_C`
(`CategoryTheory.constantSheafAdj`), so `C_K ⋙ f⁻¹` is left adjoint to `f_* ⋙ Γ_D`, and the
content of the proof is the identification `f_* ⋙ Γ_D ≅ Γ_C`. That identification is in turn
formal: `Γ_C` is corepresented by the constant sheaf on a one-element set, which is a final sheaf,
and a left exact `f⁻¹` carries a final sheaf to a final sheaf.

This is the step of Tag 093R that concerns a single constant sheaf; the passage from constant to
locally constant needs the localisations of `f`, and is not proved here. Mathlib records the
statement proved below as an open problem: see the `TODO` after
`CategoryTheory.equivCommuteConstant'` in `Mathlib/CategoryTheory/Sites/ConstantSheaf.lean`, which
asks for assumptions under which `constantSheaf` commutes with pullback of sheaves.

## Main results

* `Stacks.ConstantSheaf.isTerminal_constantSheaf_obj` — the constant sheaf on a final object of
  the coefficient category is a final sheaf.
* `Stacks.ConstantSheaf.inverseImageConstantSheafIso` — for an adjoint pair `L ⊣ R` of functors
  between the two sheaf categories with `L` preserving the final object, `C_K ⋙ L ≅ C_J`.
* `Stacks.ConstantSheaf.isConstant_obj` — such an `L` carries constant sheaves to constant
  sheaves.
* `MorphismOfTopoi.constantSheafIso` and `MorphismOfTopoi.isConstant_inverseImage` — the same for
  the inverse image of a morphism of topoi.

## References

* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u v' u'

namespace Stacks.ConstantSheaf

/-- A morphism out of a one-element set is the same thing as an element of the target. This is
`Equiv.punitArrowEquiv` transported across the identification of the morphisms of `Type w` with
functions. -/
public def punitHomEquiv (Z : Type w) : (PUnit.{w + 1} ⟶ Z) ≃ Z :=
  TypeCat.homEquiv.trans (Equiv.punitArrowEquiv Z)

/-- The morphism out of a one-element set picking out `g s` is the one picking out `s`, followed
by `g`. -/
public lemma punitHomEquiv_symm_comp {Z Z' : Type w} (s : Z) (g : Z ⟶ Z') :
    (punitHomEquiv Z').symm (g s) = (punitHomEquiv Z).symm s ≫ g := rfl

/-- The element picked out by `k ≫ g` is the image under `g` of the element picked out by `k`. -/
public lemma punitHomEquiv_comp {Z Z' : Type w} (k : PUnit.{w + 1} ⟶ Z) (g : Z ⟶ Z') :
    punitHomEquiv Z' (k ≫ g) = g (punitHomEquiv Z k) := rfl

section Terminal

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u') [Category.{v'} A] [HasWeakSheafify J A]

/-- The constant sheaf on a final object of the coefficient category is a final sheaf: the
constant *presheaf* on a final object is already a sheaf (`Presheaf.isSheaf_of_isTerminal`) and
is final among presheaves, and sheafification does not move a sheaf. -/
public def isTerminal_constantSheaf_obj {X : A} (hX : IsTerminal X) :
    IsTerminal ((constantSheaf J A).obj X) :=
  IsTerminal.ofIso (Sheaf.isTerminalTerminal J hX)
    (asIso ((sheafificationAdjunction J A).counit.app (Sheaf.terminal J hX))).symm

end Terminal

section InverseImage

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
  {L : Sheaf K (Type w) ⥤ Sheaf J (Type w)} {R : Sheaf J (Type w) ⥤ Sheaf K (Type w)}

/-- A functor between the two sheaf categories which preserves the final object carries the
constant sheaf on a one-element set to the constant sheaf on a one-element set, both being final
sheaves. -/
public def inverseImageTerminalIso (L : Sheaf K (Type w) ⥤ Sheaf J (Type w))
    [PreservesFiniteLimits L] :
    (constantSheaf J (Type w)).obj PUnit.{w + 1} ≅
      L.obj ((constantSheaf K (Type w)).obj PUnit.{w + 1}) :=
  (isTerminal_constantSheaf_obj J (Type w) Types.isTerminalPUnit).uniqueUpToIso
    (IsTerminal.isTerminalObj L _
      (isTerminal_constantSheaf_obj K (Type w) Types.isTerminalPUnit))

variable (adj : L ⊣ R)
  (ι : (constantSheaf J (Type w)).obj PUnit.{w + 1} ≅
    L.obj ((constantSheaf K (Type w)).obj PUnit.{w + 1}))
  {T : C} (hT : IsTerminal T) {T' : D} (hT' : IsTerminal T')

/-- The sections of `R F` over the final object of `D` are the sections of `F` over the final
object of `C`: both are the morphisms from the final sheaf, which `L` preserves. -/
public def pushforwardSectionsEquiv (F : Sheaf J (Type w)) :
    ((sheafSections K (Type w)).obj (op T')).obj (R.obj F) ≃
      ((sheafSections J (Type w)).obj (op T)).obj F :=
  (punitHomEquiv _).symm.trans
    (((constantSheafAdj K (Type w) hT').homEquiv PUnit.{w + 1} (R.obj F)).symm.trans
      ((adj.homEquiv ((constantSheaf K (Type w)).obj PUnit.{w + 1}) F).symm.trans
        ((Iso.homCongr ι.symm (Iso.refl F)).trans
          (((constantSheafAdj J (Type w) hT).homEquiv PUnit.{w + 1} F).trans
            (punitHomEquiv _)))))

/-- The identification `pushforwardSectionsEquiv` is natural in the sheaf `F`. -/
public lemma pushforwardSectionsEquiv_naturality {F F' : Sheaf J (Type w)} (φ : F ⟶ F')
    (s : ((sheafSections K (Type w)).obj (op T')).obj (R.obj F)) :
    pushforwardSectionsEquiv adj ι hT hT' F'
        (((sheafSections K (Type w)).obj (op T')).map (R.map φ) s) =
      ((sheafSections J (Type w)).obj (op T)).map φ
        (pushforwardSectionsEquiv adj ι hT hT' F s) := by
  simp only [pushforwardSectionsEquiv, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom,
    Category.comp_id]
  rw [punitHomEquiv_symm_comp s (((sheafSections K (Type w)).obj (op T')).map (R.map φ)),
    Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_naturality_right_symm,
    ← Category.assoc, Adjunction.homEquiv_naturality_right, punitHomEquiv_comp]

/-- Global sections on `D` of the pushforward are global sections on `C`, naturally. -/
public def pushforwardSectionsIso :
    R ⋙ (sheafSections K (Type w)).obj (op T') ≅ (sheafSections J (Type w)).obj (op T) :=
  NatIso.ofComponents (fun F => (pushforwardSectionsEquiv adj ι hT hT' F).toIso)
    fun φ => by
      ext s
      simpa using pushforwardSectionsEquiv_naturality adj ι hT hT' φ s

end InverseImage

section Main

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
  {L : Sheaf K (Type w) ⥤ Sheaf J (Type w)} {R : Sheaf J (Type w) ⥤ Sheaf K (Type w)}

/-- **The inverse image of a constant sheaf of sets is constant.** If `L ⊣ R` are functors
between the sheaf categories of two sites with final objects and `L` preserves the final object,
then `L` carries the constant sheaf on a set to the constant sheaf on that set.

Both `C_K ⋙ L` and `C_J` are left adjoint to the global sections functor of `C`, the first by
`Stacks.ConstantSheaf.pushforwardSectionsIso`, so they agree. -/
public def inverseImageConstantSheafIso (adj : L ⊣ R)
    [PreservesFiniteLimits L]
    {T : C} (hT : IsTerminal T) {T' : D} (hT' : IsTerminal T') :
    constantSheaf K (Type w) ⋙ L ≅ constantSheaf J (Type w) :=
  (((constantSheafAdj K (Type w) hT').comp adj).ofNatIsoRight
      (pushforwardSectionsIso adj (inverseImageTerminalIso L) hT hT')).leftAdjointUniq
    (constantSheafAdj J (Type w) hT)

/-- A functor between sheaf categories which is a left adjoint and preserves the final object
carries constant sheaves to constant sheaves. -/
public lemma isConstant_obj (adj : L ⊣ R)
    [PreservesFiniteLimits L]
    {T : C} (hT : IsTerminal T) {T' : D} (hT' : IsTerminal T')
    (G : Sheaf K (Type w)) [Sheaf.IsConstant K G] :
    Sheaf.IsConstant J (L.obj G) := by
  obtain ⟨E, ⟨e⟩⟩ := Sheaf.mem_essImage_of_isConstant K G
  exact Sheaf.isConstant_of_iso J
    (L.mapIso e.symm ≪≫ (inverseImageConstantSheafIso adj hT hT').app E)

end Main


end Stacks.ConstantSheaf

namespace MorphismOfTopoi

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))
  {T : C} (hT : IsTerminal T) {T' : D} (hT' : IsTerminal T')

/-- **Stacks 093R, the constant case.** The inverse image of a morphism of topoi between the
topoi of sheaves of sets on two sites with final objects carries the constant sheaf on a set to
the constant sheaf on that set. -/
public def constantSheafIso :
    constantSheaf K (Type w) ⋙ f.inverseImage ≅ constantSheaf J (Type w) :=
  have := f.preservesFiniteLimits
  Stacks.ConstantSheaf.inverseImageConstantSheafIso f.adj hT hT'

include f hT hT' in
/-- **Stacks 093R, the constant case.** The inverse image of a constant sheaf of sets along a
morphism of topoi is constant. -/
@[stacks 093R "constant sheaves of sets, for an arbitrary morphism of topoi"]
public lemma isConstant_inverseImage (G : Sheaf K (Type w)) [Sheaf.IsConstant K G] :
    Sheaf.IsConstant J (f.inverseImage.obj G) :=
  have := f.preservesFiniteLimits
  Stacks.ConstantSheaf.isConstant_obj f.adj hT hT' G

end MorphismOfTopoi

end
